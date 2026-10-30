# 任务 N4 补充说明 2（10-30 16:00，服务器整节点探针发现的缺陷）

请 `git fetch origin && git merge origin/cloud/inputs-n4b`（只新增文件）。

## 修法 23 的 Z3 内存上限会让进程直接中止（必须先修）

服务器上用你的 6810c73（`h2_triage.py`，每节点 43200 s，`--memory-mb 4500`，任务清单 `cloud-inputs/n4b/server-probes/n4_jobs.json`）跑整节点 + H2。PoolManager 18089 的两个实例（d18 f=320、d29 f=928）都在 x86 分段开头（节点开始约 5 s）被 **SIGABRT** 终止：

```
terminate called after throwing an instance of 'out_of_memory_error'
  what():  out of memory
Fatal Python error: Aborted
  z3core.py:4331 Z3_solver_check_assumptions
  z3.py:7309 check
  x86_64/cfg_state.py:95 _check
  x86_64/cfg_state.py:85 _bounded_check
  x86_64/cfg_state.py:295 _is_possible
  x86_64/cfg_state.py:249 is_possible
  x86_64/cfg_executor.py:195 _is_state_reachable
  ...
```

完整日志：`cloud-inputs/n4b/server-probes/fh-18089-d18.log`（`PYTHONFAULTHANDLER=1`）。在冻结版 PoolManager 上稳定复现（两个实例、两次运行）。

即 `z3_memory_cap()` 设的 `memory_max_size` 在 `Z3_solver_check_assumptions`（增量 / 带假设的检查）里触顶时，Z3 抛出的 `out_of_memory_error` 没有被 C API 转成 `Z3Exception`，直接 `std::terminate`。你的实验没有覆盖这条调用路径。要求：

1. 修好修法 23 / 26：保证任何受上限保护的 Z3 调用（`check`、`check(assumptions)`、增量 `PrefixSolver`、`simplify`、`model.eval` 等）触顶时都只得到 unknown / Python 异常，进程不中止。如果 `memory_max_size` 无法做到，换一种办法（例如只在非增量的新求解器上用、或改用 `max_memory` + 新求解器、或依赖节点内存预算），并说明取舍。
2. 加一个回归测试：在 `check(assumptions)` 与增量求解器上把上限设得很小，确认进程不崩、得到 unknown。
3. 在 18089 d18 上复跑整节点确认。

其余 11 个探针仍在服务器上跑，结果出来后另行补充。
