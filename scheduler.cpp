#include "common.h"
#include <iostream>
#include <set>
#include <numeric>
#include <stdexcept>
#include <algorithm>
#include <minisat/core/Solver.h>
#include <queue>
#include <functional>
#include <limits>
#include <vector>

using namespace std;

DFG* dataFlowGraph = nullptr;
vector<Op*> operations;
double time_period = 0;
vec2d<int> dependencies, usage_links;

bool validateTopologicalOrder() {
    for (const auto& statement : dataFlowGraph->stmts) {
        for (const auto& dependencyIdx : dependencies[statement->idx]) {
            if (dependencyIdx > statement->idx) {
                return false;
            }
        }
    }
    return true;
}

void reorderToTopological() {
    if (validateTopologicalOrder()) {
        return;
    }

    auto& statements = dataFlowGraph->stmts;
    int count = statements.size();

    vector<int> incomingEdges(count, 0);
    for (int i = 0; i < count; ++i) {
        for (int dep : dependencies[i]) {
            incomingEdges[i]++;
        }
    }

    queue<int> zeroIncomingEdges;
    for (int i = 0; i < count; ++i) {
        if (incomingEdges[i] == 0) {
            zeroIncomingEdges.push(i);
        }
    }

    vector<int> sortedOrder;
    sortedOrder.reserve(count);

    while (!zeroIncomingEdges.empty()) {
        int current = zeroIncomingEdges.front();
        zeroIncomingEdges.pop();
        sortedOrder.push_back(current);

        for (int successor : usage_links[current]) {
            if (--incomingEdges[successor] == 0) {
                zeroIncomingEdges.push(successor);
            }
        }
    }

    if (sortedOrder.size() < count) {
        throw runtime_error("Topological order cannot be fixed due to a cycle.");
    }

    vector<Stmt*> reorderedStatements(count, nullptr);
    for (int i = 0; i < count; ++i) {
        int originalIndex = sortedOrder[i];
        reorderedStatements[i] = statements[originalIndex];
        reorderedStatements[i]->idx = i;
    }
    statements = reorderedStatements;

    vec2d<int> updatedDependencies(count), updatedUsageLinks(count);
    for (int i = 0; i < count; ++i) {
        int originalIndex = sortedOrder[i];
        for (int dep : dependencies[originalIndex]) {
            int newDependency = reorderedStatements[dep]->idx;
            updatedDependencies[i].push_back(newDependency);
        }
        for (int use : usage_links[originalIndex]) {
            int newUsage = reorderedStatements[use]->idx;
            updatedUsageLinks[i].push_back(newUsage);
        }
    }
    dependencies = updatedDependencies;
    usage_links = updatedUsageLinks;
}

int scheduleASAP() {
    for (auto& statement : dataFlowGraph->stmts) {
        statement->start_cycle = 0;
    }

    auto& statements = dataFlowGraph->stmts;
    int maximumLatency = 0;

    for (auto& statement : statements) {
        if (dependencies[statement->idx].empty()) {
            statement->start_cycle = 1;
        } else {
            for (int predecessorIndex : dependencies[statement->idx]) {
                auto& predecessor = statements[predecessorIndex];
                int predecessorCompletion = predecessor->start_cycle + max(predecessor->op->latency - 1, 0);
                statement->start_cycle = max(statement->start_cycle, predecessorCompletion + 1);
            }
        }
        maximumLatency = max(maximumLatency, statement->start_cycle + max(statement->op->latency - 1, 0));
    }
    return maximumLatency;
}

int scheduleALAP(int asapLatency) {
    for (auto& statement : dataFlowGraph->stmts) {
        statement->start_cycle = 0;
    }

    auto& statements = dataFlowGraph->stmts;
    int earliestCycle = asapLatency;

    for (auto it = statements.rbegin(); it != statements.rend(); ++it) {
        auto& statement = *it;

        if (usage_links[statement->idx].empty()) {
            statement->start_cycle = asapLatency - (max(statement->op->latency - 1, 0));
        } else {
            int latestStart = asapLatency;
            for (int successorIndex : usage_links[statement->idx]) {
                auto& successor = statements[successorIndex];
                latestStart = min(latestStart, successor->start_cycle - max(statement->op->latency, 1));
            }
            statement->start_cycle = latestStart;
            earliestCycle = min(earliestCycle, latestStart);
        }
    }

    int latency = 0;
    for (auto& statement : statements) {
        statement->start_cycle -= (earliestCycle - 1);
        latency = max(latency, statement->start_cycle + max(statement->op->latency - 1, 0));
    }
    return latency;
}

int scheduleByList() {
    auto& statements = dataFlowGraph->stmts;
    set<int> completedStatements;
    set<int> notReady;

    for (int i = 0; i < statements.size(); ++i) {
        notReady.insert(i);
    }

    vector<int> priority(statements.size());
    for (int i = 0; i < statements.size(); ++i) {
        priority[i] = statements[i]->start_cycle;
    }
    
    for (auto& statement : dataFlowGraph->stmts) {
        statement->start_cycle = 0;
    }

    auto calculateResourceUsage = [&](int cycle, Op* operation) {
        if (operation->limit < 0) {
            return -2;
        }
        int count = 0;
        for (auto& stmt : statements) {
            if (stmt->start_cycle && stmt->op->name == operation->name &&
                cycle >= stmt->start_cycle && cycle < stmt->start_cycle + stmt->op->latency) {
                count++;
            }
        }
        return count;
    };

    auto comparator = [&](int a, int b) {
        if (priority[a] == priority[b]) return statements[a]->op->delay > statements[b]->op->delay;
        return priority[a] > priority[b];
    };
    priority_queue<int, vector<int>, decltype(comparator)> readyQueue(comparator);

    for (auto it = notReady.begin(); it != notReady.end();) {
        if (dependencies[*it].empty()) {
            readyQueue.push(*it);
            it = notReady.erase(it);
        } else {
            ++it;
        }
    }

    unordered_map<int, unordered_map<int, double>> delayByCycle;
    int currentCycle = 1;

    while (completedStatements.size() < statements.size()) {
        vector<int> scheduled;

        while (!readyQueue.empty()) {
            int idx = readyQueue.top();
            readyQueue.pop();
            auto& stmt = statements[idx];

            double& usedDelay = delayByCycle[currentCycle][idx];
            if (stmt->op->limit < 0) {
                if (stmt->op->delay + usedDelay <= time_period) {
                    stmt->start_cycle = currentCycle;
                    scheduled.push_back(idx);
                    for (int successorIndex : usage_links[idx]) {
                        auto& successor = statements[successorIndex];
                        delayByCycle[currentCycle][successor->idx] = max(delayByCycle[currentCycle][successor->idx], usedDelay + stmt->op->delay);
                    }
                } else readyQueue.push(idx);
            } else if (calculateResourceUsage(currentCycle, stmt->op) < stmt->op->limit) {
                stmt->start_cycle = currentCycle;
                scheduled.push_back(idx);
                for (int successorIndex : usage_links[idx]) {
                    auto& successor = statements[successorIndex];
                    if (successor->op->limit < 0) {
                        auto& successorDelay = delayByCycle[currentCycle + stmt->op->latency - 1][successor->idx];
                        successorDelay = max(successorDelay, stmt->op->delay);
                    }
                }
            } else {
                readyQueue.push(idx);
                break;
            }
        }

        for (int idx : scheduled) {
            completedStatements.insert(idx);
        }

        for (auto it = notReady.begin(); it != notReady.end();) {
            bool isReady = true;
            for (int dep : dependencies[*it]) {
                auto& pred = statements[dep];
                if (!completedStatements.count(dep) ||
                    (pred->start_cycle + max(pred->op->latency, 1)) > (currentCycle + 1)) {
                    isReady = false;
                    break;
                }
            }
            if (isReady) {
                readyQueue.push(*it);
                it = notReady.erase(it);
            } else {
                ++it;
            }
        }
        currentCycle++;
    }

    int finalLatency = 0;
    for (auto& statement : statements) {
        finalLatency = max(finalLatency, statement->start_cycle + max(statement->op->latency - 1, 0));
    }
    return finalLatency;
}

void schedule(DFG* graph, const vector<Op*>& operationsList, double cycleTime) {
    dataFlowGraph = graph;
    operations = operationsList;
    time_period = cycleTime;

    get_deps_and_uses(dataFlowGraph, dependencies, usage_links);
    reorderToTopological();

    int latency = scheduleASAP();
    latency = scheduleALAP(latency);
    latency = scheduleByList();

    cout << latency << endl;
}