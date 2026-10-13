# 任务 D：测试卫生两项（test-hygiene）

基于 `cloud/b3b-merged`（be4dfc7）开工。交付分支 `cloud/test-hygiene`（同一提交也推到了会话指定分支 `claude/d-test-hygiene-szkj14`）。

## 结论

1. **msize_absint 不再依赖 `tmp/prov_common.py`。** 仓库历史里从没提交过这个文件（`git log --all -- 'tmp/*'` 为空，`-S prov_common` 只命中引用它的提交），无法恢复，所以按调用点重建。`tools/msize_absint.py` 只用到 `prov_common.Prog(blocks)` 的五个字段：`entry / by_pc / succs / pads / ret_points`（原 TODO 注释里也是这么写的，并写明计划切到 `tools/call_provenance.py`）。这五个字段在 `tools/call_provenance.py::_collect_facts` 里已经全部按同一口径算好了，所以只需把它们公开出来，不需要新写分析逻辑。
   - 迁移后 `tests/unit/test_msize_absint.py` 的 **42 条全部通过**，且是在干净工作区（不存在 `tmp/` 目录）下跑的。这些测试是逐位精确断言（三合约唯一/2–4/5–16/⊤ 分布、五个热块的 msize/fmp、⊤ 源站点 28/8 个及排名第一的站点与计数 304/255、CErc20 下界直方图 594/78/31/18、继承/自产 ⊤ 计数 402/2、349/1、Safe 6275 在保守对照下退化成 ⊤ 等）。重建的 CFG 只要在 pads、返回点或后继上和原型有任何偏差，这些数字就会变，所以可以认为重建与原型行为一致。
   - 没有任何测试需要 skip。
2. **`test_offset_view_step_lemma_proves_the_rewrite_without_per_read_queries` 改为不依赖墙钟。** 原测试里的两条自检查询走 `answer()`（3s timeout）。实测其中"改写正确"那条（8 个 store 的 offset-view 链）在空载机器上就要 **2.5–3.3s**，本来就贴着 3s 的边。现在这两条查询改用确定性的 rlimit 预算（2 亿，约为实测消耗的 13 倍），仍然断言答案是 `unsat`。
   - 高负载复现（4 核机器，12 个 `yes` 忙循环）：原测试 **3/3 失败**，失败信息是 `assert unknown == unsat`（就是那条 3s 查询超时）；新测试 **5/5 通过**（每次约 11s）。空载时原测试 3/3 通过（3.1–3.4s），和任务描述一致。
3. 全量快测：见第 4 节。

## 1. 改动位置

| 文件:行 | 内容 |
|---|---|
| `tools/call_provenance.py:389-421` | 新增公开的 `ReturnAwareCfg`（字段 `entry/by_pc/succs/pads/ret_points`）和 `build_return_aware_cfg(blocks)`，内部直接调用已有的 `_collect_facts(blocks, DEFAULT_OPTIONS)`，不新增分析逻辑 |
| `tools/msize_absint.py:62-66` | 改为从 `tools.call_provenance` 导入；删掉不再使用的 `import os` / `import sys` |
| `tools/msize_absint.py:782-793` | `_load_call_provenance_module()`（往 `sys.path` 注入 `tmp/` 再 `import prov_common`）替换为 `_build_return_aware_cfg()`；`CallProvenanceError` 转换成 `MSizeAnalysisError` |
| `tools/msize_absint.py:963` | `provenance.Prog(blocks)` → `_build_return_aware_cfg(blocks)` |
| `tests/unit/test_block_uf_unification.py:22-33` | 新增 `answer_rlimit()`（只设 `rlimit`，不设 timeout）及预算依据的注释 |
| `tests/unit/test_block_uf_unification.py:371,378` | 该测试的两条自检查询从 `answer()` 改为 `answer_rlimit()`，断言仍然是 `== unsat` |

## 2. 重建依据（逐字段）

`msize_absint.analyze_memory_size` 对 `graph` 的全部用法（:963 起）：`graph.by_pc`、`graph.succs`、`graph.pads`（传给 `_pads_pushed`）、`graph.entry`、`graph.ret_points[pc]`（返回点 → 可能的返回目标集合）。

| 字段 | 取值 | 依据 |
|---|---|---|
| `entry` | `blocks[0].pc` | `analyze_memory_size` 的文档要求"入口块必须是第一个"；`call_provenance` 用的是同一个约定 |
| `by_pc` | `{b.pc: b}` | 只用于按 pc 查块 |
| `succs` | `build_evm_cfg(blocks)` 的朴素后继 | 模块文档："裸的 `build_evm_cfg` 会把每个 callee 的返回点连回所有 caller"——原型就是在裸 CFG 上叠加影子栈；`context_sensitive=False` 这个保守对照分支也正是要用裸 CFG |
| `pads` | `evm_resolved_return_sites(blocks)` | 全部活控制流 `immediate_set` 的并集。msize 自己的 `_pads_pushed` 与 `call_provenance._pads_pushed` 逐字相同，说明两者用的是同一个 pad 集合口径 |
| `ret_points` | 活控制流是带 `immediate_set` 的无条件 `JUMP` 的块 → `immediate_set`（去重保序） | msize 在返回点上只走返回边（取 `targets` 里的一个或全部），这正好是"无条件 JUMP + immediate_set"的语义 |

与原型可能的差别只有一处：`_collect_facts` 是 fail-closed 的，碰到以下三种情况会抛 `UnsupportedJumpShape`：带 `immediate_set` 的 JUMPI、动态未解析跳转、跳转目标不落在块上。现在这个异常会被转成 `MSizeAnalysisError`。三合约上这三种情况都是 0 例（`test_call_provenance` 锁着），所以不影响任何数字。

## 3. 健全性论证

- **msize_absint 本身没有证明义务**：它的结论只是专门化参数 `(msize, fmp)` 的"提议"，选错只会导致证不出或性能变差（模块文档和方案 §2.3 都这么写）。这次改动没有改变任何抽象语义（transfer、join、汇总都没动），只是换了 CFG 事实的来源，而新的来源就是深度类分析（`build_call_provenance`）已经在用的那一份。
- **新增的拒绝只会更保守**：动态未解析跳转会让 CFG 静默缺边，前向分析就会漏掉状态，可能"算出"一个过窄的唯一值。原型对这种情况怎么处理不得而知；现在一律抛 `MSizeAnalysisError`，下游拿不到任何结论，最多是证不出，不会误证。
- **rlimit 测试没有削弱检查**：断言仍然是 `== unsat`。rlimit 是 Z3 每次 `check` 独立计算的确定性计数，预算不够只会返回 `unknown`，使断言失败，不会凭空出现 `unsat`。我单独验证了两点：
  1. 同一进程里对同一查询连续调用 8 次，每次给 30M 预算都得到 `unsat`，说明预算是按单次 check 计的，不是全进程累计；
  2. 预算给到 1M 时返回 `unknown`，说明这个预算确实在起约束作用。

  测试其余部分没动：不允许走逐读 solver 证明（monkeypatch 成 `pytest.fail`）、记录下来的引理要能 SMT2 回读复核、normalize 的记录要带这条引理。生产代码 `_offset_view_step_lemma` 里的 10s timeout 也没动（实测这条查询约 0.2s，余量约 50 倍，而且每个进程只证一次）。

## 4. 测试结果

- `tests/unit/test_msize_absint.py`：42 passed（`--collect-only` 显示收集到 42 条）。
- `tests/unit/test_msize_absint.py` + `test_call_provenance.py` + `test_block_specialization.py`：94 passed（60s）。
- `tests/unit/test_block_uf_unification.py::test_offset_view_step_lemma_proves_the_rewrite_without_per_read_queries`：按节点 ID 单独跑通过；高负载下 5/5 通过。
- 全量快测 `poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider -x`：FULL_SUITE_RESULT

## 5. 离线验证数据

| 场景 | 原测试 | 新测试 |
|---|---|---|
| 空载 | 3/3 通过，每次 3.1–3.4s | 通过 |
| 4 核机器 + 12 个 `yes` 忙循环 | 3/3 失败，`assert unknown == unsat` | 5/5 通过，每次 10.5–12.4s |

rlimit 实测（z3 4.15.4）：改写查询每次 check 约 13.0–15.4M，用时 2.5–3.3s；引理回读每次约 1.0–2.2M，用时约 0.2s。

## 6. 未解决的问题

- `rlimit` 的计数在不同 Z3 版本之间不保证一致。预算是按 `poetry.lock` 锁定的 z3-solver 4.15.4 定的，并留了 13 倍余量；以后升级 Z3 时，如果这条测试变成 `unknown`，应该先重测消耗再调预算，而不是改断言。
- 同文件里其他测试仍然用 `answer()`（3s）。这次只处理了任务点名的那一条。其余用 `answer()` 的查询在本机都是亚秒级，目前没有观察到负载敏感的失败，所以没有动。
