# 任务 I 报告：Permit2 pc=1327 model_domain_nonempty 返回 unknown（permit2-domain）

分支：`cloud/permit2-domain`（基于 `cloud/inputs-permit2` = 6cc0431，代码等于冻结提交 caa01b1）。

## 1. 结论

- **公式可满足**，不是公理与入口条件冲突。`md1327.smt2` 的结构是
  `entry(7 条合取) ∧ 3 条 ULE(host_gas_sload(...), 2100 上界) ∧ 3 条 ULE(host_gas_sstore(...), 上界)`，
  没有 div_quotient 公理（公式里没有 bvudiv）。host_gas 公理只给预言函数的值设上界，
  取 `host_gas_* := 0` 就全部成立；入口部分本身 0.09s 内 sat。
- 显式模型（由新路由求出，并已用 `model.eval(F', model_completion=True)` 验证为 `True`）：
  ```
  CallDataSize = 0, CodeSizeBytes = 0, R15_mem_base = 0,
  blk1327_10_None_None_memory_size_bytes = 0, blk1327_10_None_None_x86_status = 4,
  blk1327_10_None_None_host_gas_seq_sload = 0, blk1327_10_None_None_host_gas_seq_sstore = 0,
  Storage = K(BitVec(256), 0),
  sha3_slice := λ(a, n). 0（常函数）, host_gas_sload := λ…. 0, host_gas_sstore := λ…. 0,
  其余栈/内存变量任意（取 0）
  ```
  另外，直接用"只解入口 7 条合取得到的模型 + model_completion"对**原公式**逐条 eval，19 条（simplify 后）全部为 `True`。
- **求解器解不动的原因：未解释函数以 lambda 数组为参数。** host_gas 预言的参数里含
  `sha3_slice(lambda i. mem[base+i], len)`（SHA3 读内存窗口，SLOAD/SSTORE 的 key 是 keccak 结果）。
  Z3 的数组理论遇到"UF 作用于 lambda"时不完备，只能给 `unknown (incomplete (theory array))`，
  永远不会报 sat（unsat 方向不受影响，所以期望 unsat 的配对义务没有暴露这个问题）。
  最小复现：`ULE(g(h(Lambda([i], mem[x+i]))), 100)` 单独一条，`SolverFor("QF_AUFBV")` 和默认 `Solver()` 都立即返回 unknown。
  这也解释了实测：QF_AUFBV 0.5–1.6s 报 incomplete，`_solve_query` 的回退通用 Solver 用完剩余预算仍是 unknown。
  与量词公理无关（公式里只有 lambda，没有 forall/exists）：去掉 host_gas 公理后入口部分 0.09s sat；入口加上任意单独一条 host_gas 公理（sload 或 sstore，参数含 sha3_slice(lambda)）就 unknown。

## 2. 改动位置

- `verification/block_equivalence.py:114` `_array_argument_ufs(formula)`：收集参数含数组 sort 的未解释函数（穿过 lambda/量词体）；
  若出现函数被当作值引用（`as-array`、`map` 等，decl 参数里有 FuncDecl）返回 `None`，路由直接放弃。
- `verification/block_equivalence.py:140` `sat_by_constant_array_ufs(formula, timeout_ms)`：常函数见证路由，只返回 `"sat"` 或 `"unknown"`。
- `verification/block_equivalence.py:2882` 附近，`_check` 中：`expected == "sat"` 且尚未判定时，先走见证路由（预算 `min(timeout, _QUICK_EXACT_MS=3s)`），
  仍为 unknown 再走原来的直接求解。期望 unsat 的义务完全不经过这条路。
- 新测试 `tests/unit/test_block_sat_witness.py`（10 个）。

影响面：所有 `_check(..., expected="sat")` 的调用点——`entry_nonempty`、`model_domain_nonempty`（block_equivalence 与 block_program）、
`init_nonempty`、`context_nonempty_*`（block_parallel）。没有数组参数 UF 的公式立即返回 unknown，行为与原来完全相同。

## 3. 健全性论证

设 F 为待检查公式，f₁…fₖ 为 F 中参数含数组 sort 的未解释函数，c₁…cₖ 为新鲜常量（sort 为 fᵢ 的值域）。
令 F' = F[fᵢ := λx̄. cᵢ]（`substitute_funs`，替换体是闭项，不存在变量捕获）。

1. **SAT(F') ⇒ SAT(F)。** 取 F' 的模型 M。fᵢ 不在 F' 中出现（由第 3 点保证），把 M 扩展为 M⁺：fᵢ 解释为常函数 x̄ ↦ M(cᵢ)。
   由替换引理，M⁺ ⊨ F ⟺ M⁺ ⊨ F[fᵢ := λx̄. cᵢ] = F'，而 M⁺ 与 M 在 F' 的符号上一致，故 M⁺ ⊨ F。这就是 F 的 SAT 证书。
2. **只在真的拿到模型时才算通过。** 路由要求求解器返回 `sat` **并且** `model.eval(F', model_completion=True)` 字面为 `True`；
   其它情况（unknown、unsat、eval 得到非字面量或 False）一律报 `"unknown"`。
3. **F' 中不残留 fᵢ。** `substitute_funs` 不改写高阶引用（`Map(f, a)`、`as-array`），已用 z3 4.15.4 确认 `Map(g, a)` 原样保留。
   因此 `_array_argument_ufs` 一旦发现任何 decl 参数是函数就返回 `None`，路由放弃；替换后再次检查 F' 中没有数组参数 UF（结果必须是 `[]`）。
4. **UNSAT(F') 不说明任何事**（F 可能需要 f 非常数，例如 `sha3(L1) ≠ sha3(L2)`），路由不会报 `"unsat"`，测试覆盖了这一点。
5. 这是一个"提议"类机制：限制成常函数只是挑选候选模型的方式，选错只会让路由返回 unknown、退回原直接求解，不可能导致误证；
   它从不参与期望 unsat 的义务，也不改变任何 UNSAT 结论的来源。
6. 被检查的公式本身没有变：`Obligation.formula` 仍记录原 F，`answer="sat"` 的含义仍是"F 可满足"；`lemmas` 不变。

为什么这对 model_domain_nonempty 一般都成立：`host_model_axioms` 只有 `ULE(host_gas_op(args), bound)`，`div_quotient_axioms` 是重言式；
只要入口前提本身不约束 sha3_slice/host_gas 的取值，常函数 0 就满足全部公理。代码里不依赖这个论证，而是对每个公式实际求解并校验模型。

## 4. 测试结果

- 新测试按节点 ID 单独运行：`poetry run pytest tests/unit/test_block_sat_witness.py -v` → 10 passed（0.84s），全部被收集。
  覆盖：lambda 下 UF 直接求解为 unknown；见证证明 host_gas 公理；常量取值由求解器决定（sha3_slice 必须等于 7）；
  lambda 体内嵌套的 UF 也被替换；需要非常函数时返回 unknown 而非 unsat；不可满足公式绝不报 sat；
  无数组参数 UF 立即返回；`Map(f, …)` 高阶引用被拒绝；期望 unsat 的检查不调用见证路由；
  抓取的 `md1327.smt2` 在生产 `_check(expected="sat")` 下 sat。
- 抓取公式：`check_obligation.py` 的同款脚本（改为 `expected="sat"`）→ `md1327.smt2 proved 0.4s`（修改前：30s 预算 unknown）。
- 全量快测 `poetry run pytest tests/unit -q -m "not slow" -p no:cacheprovider`：

FULLSUITE_PLACEHOLDER

## 5. 离线验证数据

PROBE_PLACEHOLDER

## 6. 未解决的问题

UNRESOLVED_PLACEHOLDER
