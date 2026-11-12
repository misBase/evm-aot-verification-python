# tests/composition：组合证明引理

这里放与具体合约、具体切片无关的纯代数引理。每条只证一次，作为其他地方信任的来源。共三类：

1. **按编译器形态建模的算术 ≡ Go 解释器**：`test_codegen_shaped_arith_composition.py`，见下表。
2. **提速 hint 恒真**：`test_eq_borrow_chain_composition.py`、`test_div_r64_quotient_fits_composition.py`。验证时作为 assumption 注入的 ground 实例本身是恒真式，不改动模型。
3. **x86 summary ≡ 模型**：`test_mul_summary_composition.py`。DIV/memgas 的形状引理在运行时由 `div_proof` / `memgas_proof` fail-closed 证明，不在本目录。

## 按编译器形态建模的算术

合约验证每次证明的是 x86 ≡ 模型。模型按 codegen 形态改写之后，和 Go 不再逐行对应，所以"模型 ≡ Go"要单独证。
x86 builtin 桥接（`_handle_builtin_div/mod/addmod`）直接复用这些模型函数，同一批引理也覆盖了桥接建模。

参照 G 是解释器所调 holiman/uint256 v1.3.2 函数的逐行转写。其中 Go 的 uint64 运算、比较和 `Neg` 用 Z3 原生算子，`udivrem` 用与模型同一个 UF。

| Opcode | 模型（`common/`） | 与 Go 的差异 | 引理 | 证法 | 状态 |
|---|---|---|---|---|---|
| MUL | `Uint256.mul_codegen_order(b, a)` | 操作数角色互换（p = 次顶）；umulStep 先加 z 再加 carry；顶 limb 逐行 hop 累加，Go 是一行求和 | `test_mul_codegen_order_matches_go_holiman_mul`（对照 `Uint256.mul_semantics` = `Int.Mul` 逐行转写），外加对 `p*q` 的具体值测试 | QF_LIA | ✅ 0.1 s |
| DIV | `div_semantics` | 64 位快路径用 x86 `div r64` 形态（零扩展到 128 位相除再截低 64 位），Go 是 uint64 `/` | `test_div_matches_go_holiman_div`（结构）+ W | BV | ✅ 1.1 s，W 见下 |
| MOD | `mod_semantics` | 同上（`%`） | `test_mod_matches_go_holiman_mod` + W | BV | ✅ 1.6 s，W 见下 |
| SDIV | `sdiv_semantics` | `_abs256` 用 limb 借位减法（Go 用 `Neg`）；分类写成 `b==0 / 同号 / 异号`，Go 是 `Sign()` 嵌套的四支 | `test_sdiv_matches_go_holiman_sdiv`：内层 Div 抽象为 F，前提 F(x,0) = F(0,y) = 0 | BV + UF | ✅ 1.0 s |
| SMOD | `smod_semantics` | `_abs256` 同上；多一个 `b==0` 早退 | `test_smod_matches_go_holiman_smod`：内层 Mod 抽象为 F，前提 F(\|a\|,0) = 0 | BV + UF | ✅ 9.5 s |
| ADDMOD | `addmod_semantics` | 分段按 `compileEVMAddMod`，没有 holiman 开头的 m≥2^192 快路径 | ① `test_addmod_matches_go_holiman_addmod_without_fast_path`：内层 Mod 抽象为 F ② `test_addmod_go_fast_path_returns_true_remainder`：快路径结果满足欧几里得刻画 | ① BV + UF ② QF_LIA | ✅ 0.4 s / 0.02 s，额外依赖 T2 |

辅助引理：

| 引理 | 内容 | 测试 | 证法 | 状态 |
|---|---|---|---|---|
| W | x86 `div r64` 形态 == 同宽 `/`、`%` | `test_model_fast_path_is_x86_div_form`（与 `_div_rem_64bit` 是同一棵 AST）+ `test_x86_div_form_equals_go_uint64_div` | 纸面证明（与位宽无关，写在 docstring）+ 8 位机器证明 | ⚠️ 64 位实例 Z3 跑 30 min 仍 unknown，未机器证明 |
| F 前提 | div(x,0) = 0，div(0,y) = 0，mod(x,0) = 0 | `test_div_mod_zero_properties` | BV | ✅ |

信任基：

- **T1**：`_HOLIMAN_UDIV_UF` / `_HOLIMAN_UDIVREM_UF` 就是 holiman `udivrem`。模型、x86 builtin 桥接、G 三处共用。
- **T2**（只有 ADDMOD 依赖）：holiman `Mod` / `udivrem` 返回数学真值余数。原因是解释器走 AddMod 快路径，而编译代码和模型走 Mod/udivrem，两条路线只能靠"二者都是真值"接上。这是编译器和解释器路线不同带来的固有依赖，不是建模方式引入的。
- 数学事实：欧几里得除法余数唯一；W 的纸面证明。

组合链：

- **DIV/MOD**：模型 =（结构引理）G[uint64 `/` 换成 x86 形态] =（W）G。
- **SDIV/SMOD**：模型 = 外层[div_semantics] =（本层引理，F 取 div_semantics）G 外层[div_semantics] =（DIV 链）G。
- **ADDMOD**：
  - 快路径以外：模型 =（①）G 慢路径[mod_semantics] =（MOD 链）G。
  - 快路径区域：G = 快路径结果 =（②）真值余数 =（T2）G 慢路径 = 模型。

不在表内的算术（不属于形态建模）：

- ADD/SUB、比较、位运算：逐行转写 holiman。比较原语另有 `tests/unit/test_uint256.py::TestUint256ComparisonGroundTruth`，对 Z3 原生算子做全符号锚定。
- MULMOD：直接用 512 位 URem 的数学定义。
- EXP：非常量指数时是 UF。
- SHL/SHR/SAR、SIGNEXTEND、BYTE：用原生算子或数学定义展开。

运行：`poetry run pytest tests/composition/test_codegen_shaped_arith_composition.py`（约 15 s）
