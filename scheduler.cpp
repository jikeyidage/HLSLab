#include "common.h"
#include "minisat/core/Solver.h"
#include <algorithm>
#include <climits>
#include <queue>
#include <vector>
#include <map>
#include <set>
using namespace std;
using namespace Minisat;

// 辅助函数：计算两个操作之间的最小时间差
int compute_min_interval(Stmt* i_stmt, Stmt* j_stmt) {
    Op* i_op = i_stmt->op;
    Op* j_op = j_stmt->op;
    
    // 如果 i 是时序运算（latency > 0），则 j 必须在 i 完成后才能开始
    // 但如果在 i 的最后一个周期，j 是组合逻辑（latency=0），可以 chaining
    if (i_op->latency > 0 && j_op->latency > 0) {
        // 两个都是时序运算，j 必须在 i 完成后的下一个周期开始
        return i_op->latency;
    } else if (i_op->latency > 0 && j_op->latency == 0) {
        // i 是时序运算，j 是组合逻辑，可以在 i 的最后一个周期开始（chaining）
        return max(i_op->latency - 1, 0);
    } else {
        // i 是组合逻辑，j 可以在同一周期开始（如果满足时钟周期约束）
        return 0;
    }
}

// SDC 求解：使用 Bellman-Ford 算法求解差分约束系统
bool solve_sdc(int n, vector<vector<pair<int, int>>>& edges, vector<int>& dist, int max_bound) {
    dist.assign(n, 0);
    
    // Bellman-Ford 算法
    for (int iter = 0; iter < n; ++iter) {
        bool updated = false;
        for (int u = 0; u < n; ++u) {
            for (auto& edge : edges[u]) {
                int v = edge.first;
                int w = edge.second;
                if (dist[u] != INT_MAX && dist[v] > dist[u] + w) {
                    dist[v] = dist[u] + w;
                    updated = true;
                }
            }
        }
        if (!updated) break;
        if (iter == n - 1 && updated) {
            // 负环检测
            return false;
        }
    }
    
    // 检查是否有超出边界的值
    for (int i = 0; i < n; ++i) {
        if (dist[i] > max_bound || dist[i] < 1) {
            return false;
        }
    }
    
    return true;
}

// 计算 ASAP 调度作为下界
void compute_asap(DFG* dfg, const vec2d<int>& deps, vector<int>& asap) {
    int n = dfg->stmts.size();
    asap.assign(n, 1);
    vector<int> in_degree(n, 0);
    
    for (int i = 0; i < n; ++i) {
        in_degree[i] = deps[i].size();
    }
    
    queue<int> q;
    for (int i = 0; i < n; ++i) {
        if (in_degree[i] == 0) {
            q.push(i);
        }
    }
    
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        
        // 找到所有依赖于 u 的操作
        for (int i = 0; i < n; ++i) {
            bool depends_on_u = false;
            for (int dep : deps[i]) {
                if (dep == u) {
                    depends_on_u = true;
                    break;
                }
            }
            
            if (depends_on_u) {
                in_degree[i]--;
                if (in_degree[i] == 0) {
                    // 找到所有依赖中最大的
                    int max_start = 1;
                    for (int dep : deps[i]) {
                        int min_interval = compute_min_interval(dfg->stmts[dep], dfg->stmts[i]);
                        max_start = max(max_start, asap[dep] + min_interval + 1);
                    }
                    asap[i] = max_start;
                    q.push(i);
                }
            }
        }
    }
}

// 计算 ALAP 调度作为上界
int compute_alap(DFG* dfg, const vec2d<int>& uses, vector<int>& alap, int max_cycle) {
    int n = dfg->stmts.size();
    alap.assign(n, max_cycle);
    vector<int> out_degree(n, 0);
    
    for (int i = 0; i < n; ++i) {
        out_degree[i] = uses[i].size();
    }
    
    queue<int> q;
    for (int i = 0; i < n; ++i) {
        if (out_degree[i] == 0) {
            q.push(i);
            alap[i] = max_cycle;
        }
    }
    
    while (!q.empty()) {
        int u = q.front();
        q.pop();
        
        // 找到所有 u 依赖的操作
        for (int i = 0; i < n; ++i) {
            bool u_depends_on = false;
            for (int use : uses[i]) {
                if (use == u) {
                    u_depends_on = true;
                    break;
                }
            }
            
            if (u_depends_on) {
                out_degree[i]--;
                if (out_degree[i] == 0) {
                    // 找到所有使用中最早的
                    int min_end = max_cycle;
                    for (int use : uses[i]) {
                        int min_interval = compute_min_interval(dfg->stmts[i], dfg->stmts[use]);
                        min_end = min(min_end, alap[use] - min_interval - 1);
                    }
                    alap[i] = min_end;
                    q.push(i);
                }
            }
        }
    }
    
    return max_cycle;
}

// 尝试在给定延迟下求解调度
bool try_schedule_with_latency(DFG* dfg, const std::vector<Op*>& ops, const std::vector<Constr*>& constrs,
                                double clock_period, int target_latency, vector<int>& result) {
    int n = dfg->stmts.size();
    
    vec2d<int> deps, uses;
    get_deps_and_uses(dfg, deps, uses);
    
    // 计算 ASAP 和 ALAP
    vector<int> asap, alap;
    compute_asap(dfg, deps, asap);
    
    int max_cycle = 0;
    for (int i = 0; i < n; ++i) {
        max_cycle = max(max_cycle, asap[i] + dfg->stmts[i]->op->latency * 10);
    }
    max_cycle += 100;
    
    compute_alap(dfg, uses, alap, max_cycle);
    
    // 调整 alap，确保 alap >= asap
    for (int i = 0; i < n; ++i) {
        alap[i] = max(alap[i], asap[i]);
        // 同时确保在目标延迟内完成
        int finish_time = alap[i] + max(dfg->stmts[i]->op->latency - 1, 0);
        if (finish_time > target_latency) {
            int required_start = target_latency - max(dfg->stmts[i]->op->latency - 1, 0);
            if (required_start < asap[i]) {
                return false; // 不可行
            }
            alap[i] = min(alap[i], required_start);
        }
    }
    
    // 使用 SAT 求解
    Solver solver;
    map<pair<int, int>, Var> var_map;
    
    // 计算最大周期数
    int max_t = 0;
    for (int i = 0; i < n; ++i) {
        max_t = max(max_t, alap[i]);
    }
    max_t += 10;
    
    // 创建变量：每个操作在其时间窗口内的每个周期
    for (int i = 0; i < n; ++i) {
        for (int t = asap[i]; t <= min(alap[i], max_t); ++t) {
            var_map[{i, t}] = solver.newVar();
        }
    }
    
    // 约束1：每个操作必须恰好在一个周期开始
    for (int i = 0; i < n; ++i) {
        vec<Lit> clause;
        for (int t = asap[i]; t <= min(alap[i], max_t); ++t) {
            if (var_map.count({i, t})) {
                clause.push(mkLit(var_map[{i, t}]));
            }
        }
        if (clause.size() > 0) {
            solver.addClause(clause);
        }
        
        // 每个操作至多在一个周期开始（互斥）
        for (int t1 = asap[i]; t1 <= min(alap[i], max_t); ++t1) {
            for (int t2 = t1 + 1; t2 <= min(alap[i], max_t); ++t2) {
                if (var_map.count({i, t1}) && var_map.count({i, t2})) {
                    solver.addClause(mkLit(var_map[{i, t1}], true), mkLit(var_map[{i, t2}], true));
                }
            }
        }
    }
    
    // 约束2：数据依赖约束
    for (int i = 0; i < n; ++i) {
        for (int j : deps[i]) {
            int min_interval = compute_min_interval(dfg->stmts[i], dfg->stmts[j]);
            for (int ti = asap[i]; ti <= min(alap[i], max_t); ++ti) {
                for (int tj = asap[j]; tj <= min(alap[j], max_t); ++tj) {
                    if (tj < ti + min_interval + 1) {
                        if (var_map.count({i, ti}) && var_map.count({j, tj})) {
                            solver.addClause(mkLit(var_map[{i, ti}], true), mkLit(var_map[{j, tj}], true));
                        }
                    }
                }
            }
        }
    }
    
    // 约束3：额外约束
    for (auto constr : constrs) {
        int op0 = constr->op_0 - 1;
        int op1 = constr->op_1 - 1;
        for (int t0 = asap[op0]; t0 <= min(alap[op0], max_t); ++t0) {
            for (int t1 = asap[op1]; t1 <= min(alap[op1], max_t); ++t1) {
                if (t0 - t1 > constr->difference) {
                    if (var_map.count({op0, t0}) && var_map.count({op1, t1})) {
                        solver.addClause(mkLit(var_map[{op0, t0}], true), mkLit(var_map[{op1, t1}], true));
                    }
                }
            }
        }
    }
    
    // 约束4：资源约束 - 对于每个资源类型
    for (auto op : ops) {
        if (op->limit == -1) continue;
        if (op->name == "load" || op->name == "store") continue;
        
        // 找出所有使用该资源的操作
        vector<int> stmt_ids;
        for (int i = 0; i < n; ++i) {
            if (dfg->stmts[i]->op == op) {
                stmt_ids.push_back(i);
            }
        }
        
        if (stmt_ids.empty()) continue;
        
        // 对于每个周期，使用该资源的操作数不能超过 limit
        for (int t = 1; t <= max_t; ++t) {
            vector<Lit> active_ops;
            for (int i : stmt_ids) {
                int latency = dfg->stmts[i]->op->latency;
                int effective_latency = max(latency, 1);
                
                // 如果操作 i 在周期 s 开始，它在周期 t 占用资源
                for (int s = max(asap[i], t - effective_latency + 1); s <= min(t, alap[i]); ++s) {
                    if (var_map.count({i, s})) {
                        active_ops.push_back(mkLit(var_map[{i, s}]));
                    }
                }
            }
            
            // 如果可能超过 limit，添加互斥约束
            if (active_ops.size() > (size_t)op->limit) {
                // 生成所有超过 limit 的组合：不能同时选择超过 limit 个操作
                for (size_t i = 0; i < active_ops.size(); ++i) {
                    for (size_t j = i + 1; j < active_ops.size(); ++j) {
                        // 使用鸽笼原理：任意 limit+1 个操作不能同时为真
                        if (i < (size_t)op->limit && j < (size_t)op->limit) {
                            continue; // 前 limit 个可以同时为真
                        }
                        // 任意两个操作，如果其中一个不在前 limit 个，它们不能同时为真
                        if (i >= (size_t)op->limit || j >= (size_t)op->limit) {
                            solver.addClause(mkLit(var(active_ops[i]), true), mkLit(var(active_ops[j]), true));
                        }
                    }
                }
            }
        }
    }
    
    // 约束5：memory 端口约束
    int memport_limit = 0;
    for (auto op : ops) {
        if (op->name == "load" || op->name == "store") {
            memport_limit = op->limit;
            break;
        }
    }
    
    if (memport_limit > 0) {
        for (int mem_idx = 0; mem_idx < dfg->num_memory; ++mem_idx) {
            vector<int> mem_stmt_ids;
            for (int i = 0; i < n; ++i) {
                if (dfg->stmts[i]->is_mem_stmt() && dfg->stmts[i]->get_arr_idx() == mem_idx) {
                    mem_stmt_ids.push_back(i);
                }
            }
            
            if (mem_stmt_ids.empty()) continue;
            
            // 对于每个周期，访问同一 memory 的操作数不能超过 limit
            for (int t = 1; t <= max_t; ++t) {
                vector<Lit> active_ops;
                for (int i : mem_stmt_ids) {
                    int latency = dfg->stmts[i]->op->latency;
                    int effective_latency = max(latency, 1);
                    
                    for (int s = max(asap[i], t - effective_latency + 1); s <= min(t, alap[i]); ++s) {
                        if (var_map.count({i, s})) {
                            active_ops.push_back(mkLit(var_map[{i, s}]));
                        }
                    }
                }
                
                if (active_ops.size() > (size_t)memport_limit) {
                    for (size_t i = 0; i < active_ops.size(); ++i) {
                        for (size_t j = i + 1; j < active_ops.size(); ++j) {
                            if (i >= (size_t)memport_limit || j >= (size_t)memport_limit) {
                                solver.addClause(mkLit(var(active_ops[i]), true), mkLit(var(active_ops[j]), true));
                            }
                        }
                    }
                }
            }
        }
    }
    
    // 约束6：时钟周期约束
    // 对于每个周期，检查组合逻辑链的延迟总和
    for (int t = 1; t <= max_t; ++t) {
        // 找出可能在周期 t 开始的所有组合逻辑操作
        vector<int> cycle_ops; // stmt_id
        for (int i = 0; i < n; ++i) {
            if (asap[i] <= t && t <= min(alap[i], max_t)) {
                if (dfg->stmts[i]->op->latency == 0) { // 只考虑组合逻辑
                    cycle_ops.push_back(i);
                }
            }
        }
        
        if (cycle_ops.size() <= 1) continue;
        
        // 构建依赖图
        map<int, vector<int>> dep_graph;
        for (int i = 0; i < n; ++i) {
            for (int j : deps[i]) {
                if (find(cycle_ops.begin(), cycle_ops.end(), i) != cycle_ops.end() &&
                    find(cycle_ops.begin(), cycle_ops.end(), j) != cycle_ops.end()) {
                    dep_graph[j].push_back(i);
                }
            }
        }
        
        // 检查每条路径的延迟总和
        set<vector<int>> invalid_paths;
        function<void(int, double, vector<int>&, set<int>&)> dfs_check = [&](int u, double delay, vector<int>& path, set<int>& visited) {
            if (visited.count(u)) return;
            visited.insert(u);
            path.push_back(u);
            delay += dfg->stmts[u]->op->delay;
            
            if (delay > clock_period) {
                // 找到违反时钟周期的路径
                invalid_paths.insert(path);
            }
            
            for (int v : dep_graph[u]) {
                dfs_check(v, delay, path, visited);
            }
            
            path.pop_back();
            visited.erase(u);
        };
        
        for (int i : cycle_ops) {
            vector<int> path;
            set<int> visited;
            dfs_check(i, 0.0, path, visited);
        }
        
        // 添加约束：不能所有操作都在同一周期
        for (auto& path : invalid_paths) {
            if (path.size() > 1) {
                vec<Lit> clause;
                for (int stmt_id : path) {
                    if (var_map.count({stmt_id, t})) {
                        clause.push(mkLit(var_map[{stmt_id, t}], true));
                    }
                }
                if (clause.size() > 1) {
                    solver.addClause(clause);
                }
            }
        }
    }
    
    // 求解 SAT
    bool sat_result = solver.solve();
    
    if (sat_result) {
        // 提取解
        result.assign(n, 1);
        for (int i = 0; i < n; ++i) {
            for (int t = asap[i]; t <= min(alap[i], max_t); ++t) {
                if (var_map.count({i, t})) {
                    if (solver.modelValue(mkLit(var_map[{i, t}])) == l_True) {
                        result[i] = t;
                        break;
                    }
                }
            }
        }
        return true;
    }
    
    return false;
}

void schedule(DFG* dfg, const std::vector<Op*>& ops, const std::vector<Constr*>& constrs, double clock_period) {
    int n = dfg->stmts.size();
    if (n == 0) return;
    
    vec2d<int> deps, uses;
    get_deps_and_uses(dfg, deps, uses);
    
    // 计算 ASAP 作为初始下界
    vector<int> asap;
    compute_asap(dfg, deps, asap);
    
    // 估算最大延迟
    int max_latency = 0;
    for (int i = 0; i < n; ++i) {
        max_latency = max(max_latency, asap[i] + dfg->stmts[i]->op->latency * 10);
    }
    max_latency += 100;
    
    // 二分搜索最小可行延迟
    int left = 1, right = max_latency;
    vector<int> best_schedule;
    
    while (left <= right) {
        int mid = (left + right) / 2;
        vector<int> result;
        
        if (try_schedule_with_latency(dfg, ops, constrs, clock_period, mid, result)) {
            best_schedule = result;
            right = mid - 1; // 尝试更小的延迟
        } else {
            left = mid + 1; // 需要更大的延迟
        }
    }
    
    // 应用最佳调度
    if (!best_schedule.empty()) {
        for (int i = 0; i < n; ++i) {
            dfg->stmts[i]->start_cycle = best_schedule[i];
        }
    } else {
        // 如果没有找到解，使用 ASAP
        for (int i = 0; i < n; ++i) {
            dfg->stmts[i]->start_cycle = asap[i];
        }
    }
}