"""cutpoint 耦合关系 R 的统一 schema（`docs/循环处理增强方案.md` §4.1/§4.3）。

## 为什么需要这个模块

归纳步在 cutpoint 上做两件事：**havoc** 出一个任意状态，然后在 latch/exit 处
**证明** R 保持。这两件事必须覆盖同一组状态分量——否则会出现这样的组合：

    某个量在 havoc 时被 by construction 耦合（两侧写同一个符号），
    但 R 的证明目标里没有它

于是该量的实际关系**从未被校验**，通用 theorem 证的是"两侧恰好相等"的那个特例，
而 certificate application 不会发现实际到达状态并不满足它。这不是降级方向，是
**假绿**方向。develop 上已实测到三处这样的缺口（host-gas 序号、`lastGasCost`、
return data），全都是"只改 havoc 不改证明目标"造成的。

因此本模块把 havoc 与 goals 绑成一对，由 :meth:`CutpointRelationSchema.
_assert_component_symmetry` 强制两者的**具名分量集合完全一致**：新增一个分量却
只改了一半，会当场抛错而不是静默放行。

**分量名齐全 ≠ R 闭合**（§4.5.5）。对称性断言比的是分量**名称集合**，看不见
分量**内部**漏掉的合取。已实测的一类内部缺口是 CALLENGINE 表示层：`build_havoc`
对每个 callEngine 字段同时写属性与 `[R13+off]` limb，而 goals 曾**全部只比较
属性** —— 于是 R 接受"属性相等、limb 陈旧"的状态，定理在同步状态上证出却被
应用到不同步状态。现由 `callengine_mirror` 分量补齐，字段清单
（``_CALLENGINE_MIRROR_FIELDS``）与 `_sync_callengine` 的实际调用在 `build_havoc`
里对账，漏一个当场抛错。

另有一类东西**不是** R 的状态等式分量，而是 cutpoint 的**结构前提**（§4.5.6）：
"两侧均处于 running"、"待消费队列为空"。status 写进 R 的等式分量是过强约束
（cutpoint 处两侧都还在 running，它的主位置是 terminal observable ②(d)），但
"都还在 running"这件事本身不能靠 `create_initial_state` 的初值 by construction
成立。这些前提由 :meth:`CutpointRelationSchema.structural_premises` 单点给出，
五处覆盖点（``CUTPOINT_STRUCTURAL_SITES``）各自核对。

## 与 develop-cycle 的关系

设计（具名分量 + 对称性断言 + fingerprint）取自 develop-cycle 的同名 schema，
但按 develop 的现实重写，三点不同：

1. **gas 进 R**。develop-cycle 把 gas 排除在关系之外，用 no-OOG envelope 压死
   x86 TAG 的错误分支——那是因为它没有 EVM 侧 gas 语义。develop 有（`GasCheck`
   三档、OOG 是真实分叉、TAG 三分支两侧对照），所以 gas 是 R 的合取。
2. **补 `host_gas_seq` 与 `return_data_source` 两个分量**，两个分支原先都缺。
3. **去掉 develop 上不存在的 SMTState 依赖**（`memory_gas_invariant_witness`
   一类的 witness 机制、`callengine_block_number` 等新增字段）。
"""

from dataclasses import dataclass
from typing import (
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    List,
    Optional,
    Sequence,
    Tuple,
)

import hashlib

from z3 import (
    And,
    BitVec,
    BitVecSort,
    BitVecVal,
    BoolVal,
    Concat,
    Extract,
    IntVal,
    Lambda,
    Or,
    Select,
    ULE,
    simplify,
)

from common.store_forwarding import unshift_store_chain
from common.uint256 import Uint256
from state.smt_state import SMTState, MemoryDomain
from state.host_gas import HOST_GAS_SEQ_KINDS
from common.identity import callable_identity
from x86_64.aot_profile import GO_HPC_EVM_PROFILE
from x86_64.models import Register

LIMBS_PER_UINT256 = 4
LIMB_SIZE_BYTES = 8
STACK_ELEMENT_SIZE = LIMBS_PER_UINT256 * LIMB_SIZE_BYTES  # 0x20

# 内存扩展 gas 的协议常量，镜像 state/evm_gas_state.py（那里是费用计算的
# 唯一权威实现；这里只重建 `lastGasCost = memoryGasCost(MSize)` 这条不变式）。
_MEMORY_GAS = 3
_QUAD_COEFF_DIV = 512

# 协议自身的内存大小上限，镜像 `evm_ir/semantics_gas.py::_MEM_SIZE_CAP`
# （`tests/unit/test_cutpoint_relation.py` 会对账两处常量，漂了就红）。
#
# `calc_mem_size_64*` 在 `requested > 该值` 时分叉到 OUT_OF_GAS，因此任何**未
# 终止**路径上都有 `MSize = 32*((requested+31)>>5) ≤ 该值`（右端取等）。这是
# 协议**自己强制**的界，也正因如此它是唯一归纳闭合的界——见
# `CutpointRelationSchema.max_memory_size_bytes` 的说明。
EVM_MEMORY_SIZE_CAP = 0x1FFFFFFFE0

# `evm_memory_gas_cost` 向 ITE 分支分发时的叶子上限。超出就退回裸公式：分发是
# 提速手段，不能自己变成指数级膨胀的来源。
_MEMORY_GAS_ITE_LEAVES = 8


def _memory_gas_cost_formula(mem_size_bytes):
    """memoryGasCost 的裸公式（不做 ITE 分发）。"""
    from z3 import Extract as _Extract, UDiv, ZeroExt, LShR

    mem_words = LShR(mem_size_bytes, BitVecVal(5, 64))
    square_128 = ZeroExt(64, mem_words) * ZeroExt(64, mem_words)
    quad_64 = _Extract(63, 0, UDiv(square_128, BitVecVal(_QUAD_COEFF_DIV, 128)))
    return mem_words * BitVecVal(_MEMORY_GAS, 64) + quad_64


def evm_memory_gas_cost(mem_size_bytes):
    """由 rounded byte size 复原 `mem.lastGasCost`。

    对齐 `state.evm_gas_state.memory_expansion_fee` 的 `new_total`：

        memWords = size >> 5          （size 已是 rounded，无需再 +31）
        newTotal = memWords*3 + memWords²/512

    quad 用 128-bit UDiv，理由同 `memory_expansion_fee`：让 `common/div_bridge.py`
    能以 `(udiv, 128)` 配上 x86 的 `div r64`（dividend 是 `Concat(RDX,RAX)`），
    64-bit UDiv 配不上会 bit-blast 到 unknown。

    **ITE 分发**（`f(If(c,a,b)) ≡ If(c, f(a), f(b))`，f 是函数 ⇒ 纯语法恒等、
    语义分毫不变）：一轮循环体之后 `MSize` 的形状是 `If(expands, rounded, old)`，
    直接代进公式会把这个 ITE 埋进 `w*w` 的**乘法内部**。QF_BV 前端 eager
    bit-blast，于是要为"操作数本身是 ITE"的 64×64 乘法器建电路——CErc20 验收用例
    实测把 `lastGasCost == memoryGasCost(MSize)` 从 0.3s 拖成 **120s unknown**。
    分发之后两支各是普通乘法，路径条件又能立刻判死一支，同一条义务 0.35s unsat。

    注意这**不是**削弱义务：分发前后是同一个公式的两种 AST 写法，证的是同一件事。
    """
    return _distribute_memory_gas_cost(mem_size_bytes, _MEMORY_GAS_ITE_LEAVES)


def _distribute_memory_gas_cost(mem_size_bytes, leaf_budget: int):
    """把 memoryGasCost 推进 `mem_size_bytes` 的 ITE 分支里（见上）。

    先 `simplify` 是必要的：执行后的 `callengine_memory_size_bytes` 是几百节点的
    未化简式，ITE 藏在里面，不化简就认不出形状（认不出时退回裸公式，只是慢，
    不影响正确性）。
    """
    from z3 import If, Z3_OP_ITE, is_app_of

    mem_size_bytes = simplify(mem_size_bytes)
    if leaf_budget > 1 and is_app_of(mem_size_bytes, Z3_OP_ITE):
        branch_budget = leaf_budget // 2
        return If(
            mem_size_bytes.arg(0),
            _distribute_memory_gas_cost(mem_size_bytes.arg(1), branch_budget),
            _distribute_memory_gas_cost(mem_size_bytes.arg(2), branch_budget),
        )
    return _memory_gas_cost_formula(mem_size_bytes)


# ---------------------------------------------------------------------------
# R 的读取器（从 loop_induction 提取，供 schema 与调用方共用）
# ---------------------------------------------------------------------------

def read_x86_stack_slot(state: SMTState, slot_from_top: int):
    """按 §4.1 的映射读取 x86 STACK 窗口中自顶向下第 j 个 slot 的 256-bit 值。

    cutpoint 都在块入口，规范窗口基址 = side-channel 的
    ``stack_base + byte_offset``（`[r13+0x38]` + `[r13+0x30]`），栈顶 slot 在
    ``base - 0x20``（负偏移）。

    **不可**混入 ``callengine_stack_pointer_limbs``（`[r13+0x28]`）：那是 host
    bridge 的传参暂存，不是窗口状态；也不用 R14 寄存器（host 调用后可能是旧值，
    靠下一块 TAG 序言重算）。
    """
    base = state.callengine_stack_base + state.callengine_stack_byte_offset
    slot_base = base - BitVecVal(STACK_ELEMENT_SIZE * (slot_from_top + 1), 64)
    limbs = [
        state.x86_memory.load_64bit(
            slot_base + BitVecVal(limb * LIMB_SIZE_BYTES, 64),
            domain=MemoryDomain.STACK,
        )
        for limb in range(LIMBS_PER_UINT256)
    ]
    # z0 是最低有效 limb（little-endian）
    return Concat(limbs[3], limbs[2], limbs[1], limbs[0])


def x86_memory_as_evm_view(x86_state: SMTState):
    """把 x86 evm_mem 转成以 EVM offset 为索引的视图：view[a] = evm_mem[R15+a]。"""
    r15 = x86_state.x86_registers.get_register(Register.R15)
    offset = BitVec("__cut_relation_mem_offset", 64)
    return Lambda([offset], Select(x86_state.x86_memory.evm_mem, r15 + offset))


def memory_coupling_condition(evm_state: SMTState, x86_state: SMTState,
                              memory_snapshot=None):
    """memory 的 R15 平移相等。

    优先把 x86 evm_mem 的 Store 链下推到 offset 空间（消 Lambda，变成 QF 纯数组
    等式）；下推失败时回退 Lambda 视图（语义相同，只是更难解）。
    """
    if memory_snapshot is not None:
        r15 = x86_state.x86_registers.get_register(Register.R15)
        unshifted = unshift_store_chain(
            x86_state.x86_memory.evm_mem, r15, memory_snapshot
        )
        if unshifted is not None:
            return evm_state.evm_memory.Memory == unshifted
    return evm_state.evm_memory.Memory == x86_memory_as_evm_view(x86_state)


def host_gas_seq_of(state: SMTState, opcode: str):
    """取该 opcode 在 state 上的调用序号，缺键返回 0。

    默认值必须与 `state.host_gas.next_host_gas_seq` 的 `counters.get(opcode,
    BitVecVal(0, 256))` 一致——两处不一致会让 R 与实际执行对不上。
    """
    return state.host_gas_seq.get(opcode, BitVecVal(0, 256))


def read_callengine_limb(state: SMTState, offset_name: str):
    """读回 `[R13 + offsets[offset_name]]` 的 64-bit limb 镜像。

    x86 侧读 callEngine 字段走 side-channel 属性快路径，只有宽度不符时才回退
    到这条内存读；因此"属性 == limb"是**表示层的一致性条件**，不是冗余。
    """
    r13 = state.x86_registers.get_register(Register.R13)
    return state.x86_memory.load_64bit(
        r13 + BitVecVal(GO_HPC_EVM_PROFILE.offsets[offset_name], 64),
        domain=MemoryDomain.CALLENGINE,
    )


# ---------------------------------------------------------------------------
# 结构前提（§4.5.6）：**不是** R 的状态等式分量
# ---------------------------------------------------------------------------

# EVM 侧的"运行中" status 取值。`error_code` 的唯一写入点是
# `evm_ir.status_code.set_terminal_status`，未终止时恒为初值 0。
#
# **0 同时是 RETURNED**，所以单看这个 8-bit 值分不出"还没终止"与"RETURN 之后
# 终止"。缺的那一半由 `error_string` 补：它同样只在 `set_terminal_status` 里被
# 写，因此 `error_string is not None` 是"已终止"的精确标记，在
# `structural_premises` 里作为 Python 层 defect 核对。
EVM_RUNNING_STATUS_CODES: FrozenSet[int] = frozenset({0})

# x86 侧多出 resumable 的那几个。host/builtin bridge 站点先写
# `[r13+0xe0] = 4/5`，Go 引擎恢复执行后**不会**把它清回 0（`cfg_executor.
# _handle_ret_with_go_bridge` 只恢复控制流，不重置状态码），所以"循环体里调用过
# host 函数"的 cutpoint 状态带着 4/5 仍然在 running。
#
# 把 running 定义成 `== 0` 在健全性上没问题，但会让所有含 host 调用的循环在
# latch 处证不出前提而无谓降级——而这条前提的本意与 status 是否为 0 无关。
X86_RUNNING_STATUS_CODES: FrozenSet[int] = frozenset({0}) | frozenset(
    GO_HPC_EVM_PROFILE.resumable_statuses
)

# 结构前提的五处覆盖点（§4.5.6）。
#
# status 不进 R 的等式分量之后，"两侧都还在 running"就只剩 `create_initial_state`
# 的初值在撑着。只写"Base 和 application"两处不够：剩下的三处仍可能靠初始值偷换，
# 于是一个已终止的状态可以冒充 cutpoint 到达状态。
CUTPOINT_STRUCTURAL_SITES: Tuple[str, ...] = (
    "base_arrival",             # ① Base 到达循环头时
    "certificate_application",  # ② 每次 certificate application
    "latch_reentry",            # ③ latch 再应用（回边回到循环头）
    "exit_edge",                # ④ 正常 exit 边上
    "exit_segment_cutpoint",    # ⑤ ③ 出口段进入下一 cutpoint 时
)


class UnknownStructuralSiteError(ValueError):
    """站点名不在 ``CUTPOINT_STRUCTURAL_SITES`` 里。

    fail-hard 而不是宽容接受：站点名打错时"核对过了"的记录会落在一个不存在的
    覆盖点上，于是真正那处覆盖点静默缺席——与只 havoc 不证同类的假绿。
    """


def running_status_condition(status, codes: Iterable[int]):
    """「该 status 字段仍处于非终止取值」。"""
    width = status.size()
    return _or_all(
        status == BitVecVal(code, width) for code in sorted(codes)
    )


@dataclass(frozen=True)
class StructuralPremiseReport:
    """一处覆盖点上的结构前提核对结果。

    拆成两栏是因为这些前提天然分两类：`conditions` 是待证的 Z3 谓词（status
    仍在 running），`defects` 是 Python 层当场可判的违例（待消费队列非空、EVM
    侧已带终止标记）。后者不能编码成 Z3 公式，混进 goals 只会被静默忽略。
    """

    site: str
    conditions: Tuple[object, ...] = ()
    defects: Tuple[str, ...] = ()

    @property
    def ok(self) -> bool:
        """Python 层没有当场违例。Z3 谓词仍须由调用方作为证明目标提交。"""
        return not self.defects


# ---------------------------------------------------------------------------
# schema
# ---------------------------------------------------------------------------

class CutpointModelRangeError(ValueError):
    """深度类合法，但超出 schema 的建模范围（如栈字节偏移越界）。

    单独成类是为了让调用方能**只**捕获它并降级为 inconclusive。裸
    `except ValueError` 会连带吞掉别处真正该 fail-hard 的编程错误——把 bug
    伪装成"这个循环证不了"是最难查的一类问题。
    """


@dataclass(frozen=True)
class RelationGoal:
    """一条具名的 R 证明义务。"""

    name: str
    condition: object


@dataclass
class RelationContext:
    """一次 havoc 的产物：状态 + 该次绑定覆盖的分量名 + 供 goals 复用的快照。"""

    state: SMTState
    bound_components: Tuple[str, ...]
    memory_snapshot: object
    stack_depth: int
    notes: Tuple[str, ...] = ()
    # havoc 时注入的**域约束**（如 `MSize ≤ 4MiB`、32 字节对齐）。
    #
    # 定理只在这些约束下成立，所以它们不是「免费的简化」而是**定理的适用域**：
    # Base 与每次 application 都必须证明实际到达状态满足它们，否则就是把定理
    # 用到了证明域之外（假绿）。`domain_predicate(state)` 把约束重述到给定
    # 状态上，供调用方当作证明目标。
    domain_constraints: Tuple[object, ...] = ()
    # 签名是 `(state, *, side=None)`：调用方知道自己拿的是哪一侧时必须传 `side`
    # （两侧的内存大小在**不同字段**上，见 `_domain_predicate`）；不知道时省略，
    # 谓词会同时约束两种表示。
    domain_predicate: Optional[Callable[..., List[object]]] = None
    # havoc 时注入的**结构前提**（§4.5.6：两侧均 running）。与 domain_constraints
    # 同机制、同理由：定理只在这些前提下成立，五处覆盖点都必须在实际状态上重新
    # 核对，否则就是把定理用到了证明域之外。
    structural_constraints: Tuple[object, ...] = ()
    structural_predicate: Optional[
        Callable[..., StructuralPremiseReport]
    ] = None


class CutpointRelationSchema:
    """成对生成 cutpoint 的 havoc 绑定与 R 证明义务。

    ``_COMPONENTS`` 是唯一的真相来源：`build_havoc` 必须绑定其中每一项，
    `component_goals` 必须为其中每一项产出义务，`_assert_component_symmetry`
    在每次 `component_goals` 时校验两者一致。
    """

    version = "cutpoint-r-develop-v2-mirror-closure-running-premise"

    _COMPONENTS: Tuple[str, ...] = (
        "stack_geometry",
        "live_stack_prefix",
        "memory",
        "memory_size",
        "memory_gas",
        "gas",
        "host_gas_seq",
        "return_data_source",
        "storage",
        "transient_storage",
        "return_metadata",
        "environment",
        "callengine_environment",
        "callengine_mirror",
    )

    # 经 `_sync_callengine` 维护的镜像字段：(side-channel 属性, profile offset 名)。
    #
    # 这份清单是 `callengine_mirror` 分量的义务来源，也是 `build_havoc` 的对账
    # 依据：`_sync_callengine` 实际同步的字段集合必须与它逐字相等，多一个少一个
    # 都当场抛错。少一个就是 §4.5.5 的那类内部缺口——分量名在、义务里却没有它，
    # 对称性断言看不见（它只比名称集合）。
    _CALLENGINE_MIRROR_FIELDS: Tuple[Tuple[str, str], ...] = (
        ("callengine_stack_byte_offset", "stack_byte_offset"),
        ("callengine_memory_size_bytes", "memory_size"),
        ("callengine_memory_gas_used", "last_gas_cost"),
        ("callengine_gas_remaining", "gas_remaining"),
        ("callengine_return_data_size_bytes", "return_data_size"),
        ("callengine_return_data_pointer", "return_data_pointer"),
    )

    # 真正只读的语义环境。**故意剔除 `return_data`**：SMTState.ENVIRONMENT_FIELDS
    # 把它列在里面，但它并不只读——CALL 族每次调用后都会被重写（EVM 侧
    # `semantics._update_call_return_data_source`，x86 侧
    # `go_function_semantics._update_return_data_source`）。它由独立的
    # `return_data_source` 分量负责，连同 pointer/size 一起。
    _READONLY_ENVIRONMENT_FIELDS: Tuple[str, ...] = tuple(
        field for field in SMTState.ENVIRONMENT_FIELDS if field != "return_data"
    )

    # 循环体内不会被改写、但 suffix 可能读到的 callEngine 只读字段。
    # return_data 的 pointer/size 不在此列（见上）。
    _CALLENGINE_ENVIRONMENT_FIELDS: Tuple[str, ...] = (
        "callengine_self_address_pointer",
        "callengine_origin_address_pointer",
        "callengine_caller_address_pointer",
        "callengine_input_pointer",
        "callengine_input_size_bytes",
        "callengine_code_pointer",
        "callengine_code_size_bytes",
        "callengine_callvalue",
    )

    def __init__(
        self,
        *,
        max_stack_byte_offset: int = 0x4000,
        max_memory_size_bytes: int = EVM_MEMORY_SIZE_CAP,
        persistent_invariants: Iterable[
            Callable[[SMTState, SMTState], Iterable[object]]
        ] = (),
    ) -> None:
        """
        Args:
            max_memory_size_bytes: 域约束 `MSize ≤ 该值` 的上界，默认取协议自身的
                内存大小上限 `EVM_MEMORY_SIZE_CAP`。

                **必须是 `calc_mem_size_64` 那个 cap，不能随手挑一个"够大"的数**：
                域约束要在回边/出口处**闭合**（域内进、域内出），否则下一轮就在
                域外复用了只在域内成立的定理。旧默认值 0x400000（4 MiB）不闭合
                —— 循环体里一条 offset 为符号量的 MSTORE 就能把 MSize 顶到 4 MiB
                以上，CErc20 验收用例实测在 latch 与 exit 两处都 SAT。协议 cap
                则闭合：超过它的 `requested` 会被 `calc_mem_size_64` 分叉成
                OUT_OF_GAS 终态，未终止路径上恒有 `MSize ≤ cap`（同一用例实测
                两侧、latch/exit 全 unsat）。

                放宽上界是**健全方向**（前提更弱 ⇒ 定理适用域更大），且 Base 与
                每次 application 仍要在实际到达状态上重新证明它——不是把义务删掉。
        """
        self.max_stack_byte_offset = max_stack_byte_offset
        self.max_memory_size_bytes = max_memory_size_bytes
        self.persistent_invariants = tuple(persistent_invariants)
        self._counter = 0

    # -- 元信息 -----------------------------------------------------------

    @property
    def component_names(self) -> Tuple[str, ...]:
        return self._COMPONENTS

    @property
    def supports_msize(self) -> bool:
        """R 是否钉住了 MSize。

        `SegmentStructuralValidator` 用它决定段内可达的 `MSIZE` opcode 是否
        可接受：MSize 不在 R 里时，havoc 后两侧的 MSize 互不相关，读它就会
        产生伪 SAT。
        """
        return "memory_size" in self._COMPONENTS

    @property
    def fingerprint(self) -> str:
        """证书缓存键的一部分。

        分量集合、只读字段集合、`HOST_GAS_SEQ_KINDS` 都进指纹：序号语义随
        `HOST_GAS_SEQ_KINDS` 的增删而变，按旧集合证出的证书不能被新集合复用。

        镜像字段清单与结构前提（覆盖点、running 取值集合）同样进指纹：它们改变
        的是**定理的适用域**，按旧适用域签发的证书不能在新适用域下复用。补上
        镜像闭包会让现有缓存证书全部失效——那是正确行为，旧证书本就在一个不闭合
        的 R 下签发。
        """
        payload = (
            self.version,
            self._COMPONENTS,
            self._READONLY_ENVIRONMENT_FIELDS,
            self._CALLENGINE_ENVIRONMENT_FIELDS,
            self._CALLENGINE_MIRROR_FIELDS,
            CUTPOINT_STRUCTURAL_SITES,
            tuple(sorted(EVM_RUNNING_STATUS_CODES)),
            tuple(sorted(X86_RUNNING_STATUS_CODES)),
            tuple(sorted(HOST_GAS_SEQ_KINDS)),
            self.max_stack_byte_offset,
            self.max_memory_size_bytes,
            # 用不会碰撞的可调用身份：lambda / 具名闭包 / 绑定方法的
            # `__qualname__` 都可能相同，两个语义不同的 schema 会共用指纹，
            # 从而复用未证明当前持久不变式的定理（假绿）。
            tuple(
                callable_identity(inv) for inv in self.persistent_invariants
            ),
        )
        return hashlib.sha256(repr(payload).encode("utf-8")).hexdigest()

    # -- havoc ------------------------------------------------------------

    def build_havoc(
        self,
        stack_depth: int,
        *,
        byte_offset_value: Optional[int] = None,
        prefix: Optional[str] = None,
        host_gas_uf_enabled: bool = False,
        abstract_calldataload_words: bool = False,
        assume_calldata_offset_no_overflow: bool = True,
    ) -> RelationContext:
        """构造 havoc 后的 cutpoint 状态（§4.3）。

        纪律：**跨轮次演化的量一律给任意共享符号，绝不给具体常量**。给常量不是
        过近似而是欠近似——它把定理钉死在初始轮，属假绿方向。本方法覆盖的三个
        易错点：

        - `host_gas_seq` 若沿用 `create_initial_state` 的空 dict，`next_host_gas_seq`
          缺键默认 0，归纳步证的就只是"从第 0 次 host 调用开始的一轮"；
        - return-data size 若沿用 `create_initial_state(return_data_size_bytes=0)`
          的具体 0，循环**之前**执行过 CALL 的场景就被排除在定理适用域外；
        - memory size / `lastGasCost` 同理（第 n 轮到达时内存已增长）。

        Args:
            host_gas_uf_enabled: 必须与调用方的 `GasCheck` 档位一致。
                `create_initial_state()` 默认把它置 **False**，若不在这里恢复，
                循环体含 SLOAD/CALL/CREATE 等 host-gas opcode 时，归纳定理就
                会在"完全不扣 host cost"的语义上证明——那与真实执行的路径集
                不同，可能漏掉 host 参数传错、OOG 阈值偏移与 gas 终值差异。

        Returns:
            RelationContext，其中 `bound_components` 必须与 `_COMPONENTS` 一致。
        """
        if prefix is None:
            self._counter += 1
            prefix = f"cut{self._counter}"

        state = SMTState.create_initial_state(num_inputs=0)
        state.host_gas_uf_enabled = host_gas_uf_enabled
        # calldata 语义开关同样必须与调用方一致：Base 用调用方的初始状态，而
        # ②/③ 的 havoc 若回到默认值，含 CALLDATALOAD/COPY 的循环就会在**另一套
        # calldata 语义**下证出定理，再被应用到 Base 的语义上（假绿）。
        state.abstract_calldataload_words = abstract_calldataload_words
        state.assume_calldata_offset_no_overflow = (
            assume_calldata_offset_no_overflow
        )
        r13 = state.x86_registers.get_register(Register.R13)
        offsets = GO_HPC_EVM_PROFILE.offsets
        bound: List[str] = []
        mirrored: List[Tuple[str, str]] = []

        def _sync_callengine(field: str, offset_name: str, value) -> None:
            """字段与 `[r13+off]` limb 同步写。

            x86 侧读该字段走 side-channel 快路径直接取属性，limb 只是宽度不符时
            回退内存读用的镜像；两者分叉即陈旧值假绿。

            同步只保证 **havoc 状态**上两者相等；实际到达状态上"属性 == limb"是
            `callengine_mirror` 分量的证明义务（§4.5.5）。这里顺带记账，供下面与
            ``_CALLENGINE_MIRROR_FIELDS`` 对账。
            """
            setattr(state, field, value)
            state.x86_memory = state.x86_memory.store_limb(
                r13 + BitVecVal(offsets[offset_name], 64),
                value,
                domain=MemoryDomain.CALLENGINE,
            )
            mirrored.append((field, offset_name))

        # --- stack_geometry ---------------------------------------------
        # **绝对深度类模式**：cutpoint 处栈深是 k，栈基字节偏移就该是 k*0x20，
        # 对应 AOT 的 `mov r14,[r13+0x38]; add r14,[r13+0x30]` 重算结果。
        #
        # 旧实现这里给的是符号 offset ∈ [k*0x20, 0x4000]，那是 no-stack-limit
        # envelope 的实现——用符号 offset 把 TAG 序言的栈下溢/超限检查泡开成
        # 不确定，再靠 envelope 假设压死。envelope 已取消（栈错误改由 ②(d)
        # 作为 terminal outcome 配对证明），符号 offset 随之废弃：具体值让
        # TAG 的栈检查静态可解，公式显著变简，且与 stack_geometry 义务自洽。
        expected_offset = stack_depth * STACK_ELEMENT_SIZE
        if byte_offset_value is None:
            byte_offset_value = expected_offset
        elif byte_offset_value != expected_offset:
            raise CutpointModelRangeError(
                "absolute depth class requires stack byte offset "
                f"{expected_offset} for depth {stack_depth}, "
                f"got {byte_offset_value}"
            )
        if byte_offset_value > self.max_stack_byte_offset:
            raise CutpointModelRangeError(
                f"stack byte offset 0x{byte_offset_value:x} exceeds the "
                f"schema bound 0x{self.max_stack_byte_offset:x}; "
                "深度类超出可建模范围，调用方应降级而不是放宽这里"
            )
        byte_offset = BitVecVal(byte_offset_value, 64)
        _sync_callengine(
            "callengine_stack_byte_offset", "stack_byte_offset", byte_offset
        )
        window_base = state.callengine_stack_base + byte_offset
        state.x86_registers.set_register(Register.R14, window_base)
        state.x86_registers.set_register(Register.R15, state.callengine_memory_base)
        bound.append("stack_geometry")

        # --- live_stack_prefix ------------------------------------------
        from verification.memory_mapping import StackMemoryMapper

        values = [
            Uint256.symbolic(f"{prefix}_stack_{index}").to_bv256()
            for index in range(stack_depth)
        ]
        for value in values:
            state.evm_stack = state.evm_stack.push(value)
        state.x86_memory = StackMemoryMapper.initialize_x86_memory_from_stack(
            state.x86_memory, values, base=window_base
        )
        bound.append("live_stack_prefix")

        # --- memory / memory_size / memory_gas ---------------------------
        from z3 import Array as _Array

        memory_snapshot = _Array(
            f"{prefix}_evm_mem0", BitVecSort(64), BitVecSort(8)
        )
        state.evm_memory.Memory = memory_snapshot
        r15 = state.callengine_memory_base
        addr = BitVec(f"{prefix}_mem_addr", 64)
        state.x86_memory.evm_mem = Lambda(
            [addr], Select(memory_snapshot, addr - r15)
        )
        bound.append("memory")

        mem_size = BitVec(f"{prefix}_memory_size_bytes", 64)
        # **这两条是定理的适用域，不是免费简化**：Base/application 必须在实际
        # 到达状态上重新证明它们（见 RelationContext.domain_predicate）；②
        # 还要在回边/出口处证明它们**闭合**（域内进、域内出）。上界取协议 cap
        # 而不是某个"够大"的常数，正是为了这个闭合性——理由见 `__init__`。
        domain_constraints = [
            ULE(mem_size, BitVecVal(self.max_memory_size_bytes, 64)),
            mem_size & BitVecVal(0x1F, 64) == BitVecVal(0, 64),
        ]
        for constraint in domain_constraints:
            state.add_assumption(constraint)
        state.evm_memory.MSize = mem_size
        _sync_callengine("callengine_memory_size_bytes", "memory_size", mem_size)
        bound.append("memory_size")

        # lastGasCost 不独立 havoc：它是 MSize 的函数（`memory_expansion_fee` 的
        # 两条分支都保持 `lastGasCost = memoryGasCost(MSize)`），独立 havoc 会
        # 过近似成"下一轮扣费任意"，制造无谓降级。
        _sync_callengine(
            "callengine_memory_gas_used",
            "last_gas_cost",
            evm_memory_gas_cost(mem_size),
        )
        bound.append("memory_gas")

        # --- gas ---------------------------------------------------------
        # 两侧共享同一符号（by construction 耦合）。这是 R 的**内部控制流关系**，
        # 三档 GasCheck 都需要——没有它两侧 OOG 分叉无法对齐、归纳不闭合。
        # 注意：Base 与每次 certificate application 必须对实际到达状态**重新
        # 证明**该等式，不得继续 by construction（§4.3）。
        gas_remaining = BitVec(f"{prefix}_gas_remaining", 64)
        state.evm_gas.Gas = gas_remaining
        _sync_callengine("callengine_gas_remaining", "gas_remaining", gas_remaining)
        bound.append("gas")

        # --- host_gas_seq -------------------------------------------------
        # 任意共享符号，**不是** 0：见方法 docstring。
        for opcode in sorted(HOST_GAS_SEQ_KINDS):
            state.host_gas_seq[opcode] = BitVec(
                f"{prefix}_host_gas_seq_{opcode.lower()}", 256
            )
        bound.append("host_gas_seq")

        # --- return_data_source -------------------------------------------
        # 内容 Array + size + pointer 全部符号化。size 不能沿用初始的具体 0。
        return_data = _Array(
            f"{prefix}_return_data", BitVecSort(64), BitVecSort(8)
        )
        state.return_data = return_data
        return_data_size = BitVec(f"{prefix}_return_data_size", 64)
        _sync_callengine(
            "callengine_return_data_size_bytes",
            "return_data_size",
            return_data_size,
        )
        _sync_callengine(
            "callengine_return_data_pointer",
            "return_data_pointer",
            BitVec(f"{prefix}_return_data_pointer", 64),
        )
        bound.append("return_data_source")

        # --- storage / transient / return_metadata ------------------------
        # 这三项由 create_initial_state 的共享 Array/字段天然耦合，无需重写；
        # 但仍要登记为已绑定，否则对称性断言会把它们当遗漏。
        bound.append("storage")
        bound.append("transient_storage")
        bound.append("return_metadata")

        # --- environment / callengine_environment -------------------------
        # 同上：只读环境在两侧是同一批 Z3 常量。
        bound.append("environment")
        bound.append("callengine_environment")

        # --- callengine_mirror --------------------------------------------
        # 上面每一次 `_sync_callengine` 都记了账，这里与声明清单对账。对不上就
        # 抛错：新加一个 `_sync_callengine` 字段却忘了列进 `_CALLENGINE_MIRROR_
        # FIELDS`，该字段的 limb 就又回到"只耦合不列义务"的状态，而分量对称性
        # 断言（只比名称集合）看不见它。
        self._assert_mirror_coverage(mirrored)
        bound.append("callengine_mirror")

        # --- 结构前提：两侧均处于 running（§4.5.6）--------------------------
        # status **不进 R 的等式分量**：cutpoint 处两侧都还在 running，写
        # `error_code == callengine_status_code` 是过强约束，只制造无谓降级；
        # 它的主位置是 terminal observable ②(d)。
        #
        # 但"都还在 running"这件事不能靠 `create_initial_state` 把两侧 status
        # 都初始化成 0 来 by construction 成立——那是把一条前提偷换成初值。做法
        # 与域约束一致：在 havoc 里显式记成假设，在五处覆盖点上作为义务重新核对。
        #
        # x86 侧给**新鲜符号**而不是沿用具体 0：bridge 返回后状态码停在 4/5，
        # status 是跨轮次演化的量，钉成 0 会把定理钉死在"本轮之前没调过 host
        # 函数"，属欠近似。EVM 侧的 running 只有 0 这一个取值（`error_code` 的
        # 唯一写入点是 set_terminal_status），保持具体 0 就是忠实的。
        state.callengine_status_code = BitVec(f"{prefix}_x86_status", 8)
        structural_constraints = [
            running_status_condition(
                state.error_code, EVM_RUNNING_STATUS_CODES
            ),
            running_status_condition(
                state.callengine_status_code, X86_RUNNING_STATUS_CODES
            ),
        ]
        for constraint in structural_constraints:
            state.add_assumption(constraint)

        notes = (
            f"stack byte offset <= 0x{self.max_stack_byte_offset:x}",
            f"memory size <= 0x{self.max_memory_size_bytes:x}",
            "gas is relational (in R), not an envelope assumption",
            "both sides are running (structural premise, not an R component)",
        )
        max_memory = self.max_memory_size_bytes

        def _domain_predicate(
            target: SMTState, *, side: Optional[str] = None
        ) -> List[object]:
            """把域约束重述到给定状态上（Base/application/latch/exit 的义务）。

            **必须按侧取正确的字段。** 两侧的"内存大小"落在**不同**字段上：
            EVM 侧是语义字段 `evm_memory.MSize`（`evm_ir.semantics_gas.
            charge_dynamic_gas` 的唯一写入点），`callengine_memory_size_bytes`
            只是 callEngine 的镜像、EVM 语义**从不写它**；x86 侧恰好相反。

            旧实现两侧都读镜像字段，于是 EVM 侧那一半读到的永远是 havoc 原值
            —— 而域约束在 havoc 里已被 `add_assumption`，义务因此**恒真**。
            CErc20 验收用例实测：出口边上 EVM 侧域目标 `simplify` 成 True，x86
            侧才是真检查。那不是"两侧都证过"，是只证了一侧；§4.4 ② 那句"不能
            靠 R 的 memory_size 分量省掉一侧"被字段混淆悄悄绕过了。

            `side` 省略时**两种表示都约束**：单参调用点（如失败诊断）看不出手里
            是哪一侧的状态，只挑一个字段必然在另一侧退化回 vacuous 检查。多出来
            的那条在对应侧读到的是未被改写的 havoc 值，恒成立，不会制造无谓降级。
            """
            if side not in (None, "evm", "x86"):
                raise ValueError(
                    f"unknown cutpoint domain side {side!r}; "
                    "expected 'evm', 'x86' or None (both representations)"
                )
            sizes = []
            if side in (None, "evm"):
                sizes.append(target.evm_memory.MSize)
            if side in (None, "x86"):
                sizes.append(target.callengine_memory_size_bytes)
            conditions: List[object] = []
            for size in sizes:
                conditions.append(ULE(size, BitVecVal(max_memory, 64)))
                conditions.append(
                    size & BitVecVal(0x1F, 64) == BitVecVal(0, 64)
                )
            return conditions

        return RelationContext(
            state=state,
            bound_components=tuple(bound),
            memory_snapshot=memory_snapshot,
            stack_depth=stack_depth,
            notes=notes,
            domain_constraints=tuple(domain_constraints),
            domain_predicate=_domain_predicate,
            structural_constraints=tuple(structural_constraints),
            structural_predicate=self.structural_premises,
        )

    def _assert_mirror_coverage(
        self, mirrored: Sequence[Tuple[str, str]]
    ) -> None:
        """`_sync_callengine` 的实际调用必须与镜像字段清单逐字相等。"""
        actual = tuple(sorted(mirrored))
        declared = tuple(sorted(self._CALLENGINE_MIRROR_FIELDS))
        if actual != declared:
            missing = sorted(set(declared) - set(actual))
            extra = sorted(set(actual) - set(declared))
            raise AssertionError(
                "callEngine 镜像字段清单与 _sync_callengine 实际调用不一致: "
                f"缺 {missing}, 多 {extra}"
            )

    # -- 结构前提 -----------------------------------------------------------

    def structural_premises(
        self, evm_state: SMTState, x86_state: SMTState, *, site: str
    ) -> StructuralPremiseReport:
        """一处覆盖点上的 cutpoint 结构前提（§4.5.6）。

        这些**不是** R 的状态等式分量，所以不进 `_COMPONENTS`、不参与分量对称性
        断言；它们是"这个状态确实是一个 cutpoint 到达状态"的结构条件：

        1. 两侧均处于 running（未终止）——见 ``*_RUNNING_STATUS_CODES``；
        2. cutpoint 位于块边界，故 `pending_errors` / `pending_constraints`
           两条待消费队列必须为空。队列非空意味着上一条指令的错误分支或路径
           约束还没被 executor 消费，此时的状态既不是块边界状态、其路径条件也
           还不完整，拿它当 cutpoint 到达状态会漏掉整条错误路径。

        Args:
            site: ``CUTPOINT_STRUCTURAL_SITES`` 之一。写死枚举是为了让"某处没
                核对"变成可检查的事实——见 `UnknownStructuralSiteError`。
        """
        if site not in CUTPOINT_STRUCTURAL_SITES:
            raise UnknownStructuralSiteError(
                f"unknown cutpoint structural site {site!r}; "
                f"expected one of {list(CUTPOINT_STRUCTURAL_SITES)}"
            )

        conditions = (
            running_status_condition(
                evm_state.error_code, EVM_RUNNING_STATUS_CODES
            ),
            running_status_condition(
                x86_state.callengine_status_code, X86_RUNNING_STATUS_CODES
            ),
        )

        defects: List[str] = []
        # `error_string` 与 `error_code` 由 set_terminal_status 单点同写，因此
        # 它能抓住 Z3 谓词抓不到的那一半：RETURNED 的码值恰好等于 running 哨兵 0。
        if getattr(evm_state, "error_string", None) is not None:
            defects.append(
                f"EVM side already terminated "
                f"(error_string={evm_state.error_string!r})"
            )
        for label, state in (("EVM", evm_state), ("x86", x86_state)):
            for queue in ("pending_errors", "pending_constraints"):
                items = getattr(state, queue, None)
                if items:
                    defects.append(
                        f"{label} side has {len(items)} unconsumed {queue} "
                        "entries; a cutpoint sits on a block boundary"
                    )
        return StructuralPremiseReport(
            site=site, conditions=conditions, defects=tuple(defects)
        )

    # -- goals -------------------------------------------------------------

    def component_goals(
        self,
        evm_state: SMTState,
        x86_state: SMTState,
        stack_depth: int,
        *,
        context: Optional[RelationContext] = None,
        memory_snapshot=None,
    ) -> Tuple[RelationGoal, ...]:
        """产出与 `_COMPONENTS` 一一对应的 R 证明义务。

        `context` 只在**归纳步**（对 havoc 状态求义务）传：它触发分量对称性
        断言。Base 与 certificate application 是对**实际到达状态**重新证明
        R（§4.3），那里没有 havoc 绑定可比，应改传 `memory_snapshot`——伪造
        一个"全绑定"的 context 会让守卫恒过，等于把它关掉。
        """
        if context is not None and memory_snapshot is not None:
            raise ValueError("context 与 memory_snapshot 互斥：前者已含快照")
        if context is not None:
            memory_snapshot = context.memory_snapshot
        r14 = x86_state.x86_registers.get_register(Register.R14)
        r15 = x86_state.x86_registers.get_register(Register.R15)

        goals: Dict[str, object] = {
            "stack_geometry": And(
                evm_state.evm_stack.SP == IntVal(stack_depth),
                x86_state.callengine_stack_byte_offset
                == BitVecVal(stack_depth * STACK_ELEMENT_SIZE, 64),
                r14
                == x86_state.callengine_stack_base
                + x86_state.callengine_stack_byte_offset,
                r15 == x86_state.callengine_memory_base,
            ),
            "live_stack_prefix": _and_all(
                evm_state.evm_stack.peek(index)
                == read_x86_stack_slot(x86_state, index)
                for index in range(stack_depth)
            ),
            "memory": memory_coupling_condition(
                evm_state, x86_state, memory_snapshot
            ),
            "memory_size": (
                evm_state.evm_memory.MSize
                == x86_state.callengine_memory_size_bytes
            ),
            # 两侧 lastGasCost 相等 **且** 各自是 MSize 的函数。只证两侧相等是
            # 健全性最低要求；补上派生不变式才能让 havoc 不过近似（§4.1）。
            "memory_gas": And(
                evm_state.callengine_memory_gas_used
                == x86_state.callengine_memory_gas_used,
                x86_state.callengine_memory_gas_used
                == evm_memory_gas_cost(x86_state.callengine_memory_size_bytes),
            ),
            "gas": evm_state.evm_gas.Gas == x86_state.callengine_gas_remaining,
            "host_gas_seq": _and_all(
                host_gas_seq_of(evm_state, opcode)
                == host_gas_seq_of(x86_state, opcode)
                for opcode in sorted(HOST_GAS_SEQ_KINDS)
            ),
            "return_data_source": And(
                evm_state.return_data == x86_state.return_data,
                evm_state.callengine_return_data_size_bytes
                == x86_state.callengine_return_data_size_bytes,
                evm_state.callengine_return_data_pointer
                == x86_state.callengine_return_data_pointer,
            ),
            "storage": (
                evm_state.evm_storage.Storage == x86_state.evm_storage.Storage
            ),
            "transient_storage": (
                evm_state.evm_transient_storage.TransientStorage
                == x86_state.evm_transient_storage.TransientStorage
            ),
            "return_metadata": And(
                evm_state.return_offset == x86_state.return_offset,
                evm_state.return_length == x86_state.return_length,
            ),
            "environment": _and_all(
                getattr(evm_state, field) == getattr(x86_state, field)
                for field in self._READONLY_ENVIRONMENT_FIELDS
            ),
            "callengine_environment": _and_all(
                [
                    *(
                        getattr(evm_state, field) == getattr(x86_state, field)
                        for field in self._CALLENGINE_ENVIRONMENT_FIELDS
                    ),
                    # 跨视图链接：EVM 指令读语义字段，生成的 x86 读 callEngine
                    # 编码。只做两侧同名字段相等，会允许两个 side channel 一起
                    # 漂移。
                    x86_state.callengine_input_size_bytes == evm_state.calldatasize,
                    x86_state.callengine_callvalue
                    == Extract(63, 0, evm_state.callvalue),
                    Extract(255, 64, evm_state.callvalue) == BitVecVal(0, 192),
                ]
            ),
            # 表示层闭包（§4.5.5）：其余分量把 EVM 属性与 x86 属性对上，这一条
            # 再把 x86 属性与它在 `[R13+off]` 的 limb 镜像对上，R 才闭合——否则
            # 定理在"属性 == limb"的 havoc 状态上证出，却可以被应用到 limb 陈旧
            # 的实际状态（定理用到了证明域之外，假绿方向）。
            #
            # **只对 x86 侧**：limb 只有 x86 侧会读（宽度不符时的回退路径），
            # EVM 侧从不碰 x86_memory，而 `evm_ir/semantics{,_gas}.py` 又会把
            # `callengine_memory_gas_used` / return-data 指针当普通标量改写、
            # 不同步 limb。对 EVM 侧强求这条只会制造必然失败的义务。
            "callengine_mirror": _and_all(
                read_callengine_limb(x86_state, offset_name)
                == getattr(x86_state, field)
                for field, offset_name in self._CALLENGINE_MIRROR_FIELDS
            ),
        }

        relation_goals = tuple(
            RelationGoal(name, goals[name]) for name in self._COMPONENTS
        )
        if context is not None:
            self._assert_component_symmetry(context, relation_goals)
        return relation_goals

    def goals(
        self,
        evm_state: SMTState,
        x86_state: SMTState,
        stack_depth: int,
        *,
        context: Optional[RelationContext] = None,
        memory_snapshot=None,
    ) -> List[object]:
        """`component_goals` 的条件列表形式（调用方通常只要条件）。"""
        conditions = [
            goal.condition
            for goal in self.component_goals(
                evm_state, x86_state, stack_depth,
                context=context, memory_snapshot=memory_snapshot,
            )
        ]
        for invariant in self.persistent_invariants:
            conditions.extend(invariant(evm_state, x86_state))
        return conditions

    # -- 对称性 -------------------------------------------------------------

    def _assert_component_symmetry(
        self, context: RelationContext, relation_goals: Sequence[RelationGoal]
    ) -> None:
        """havoc 绑定的分量集合必须与证明义务的分量集合完全一致。

        这是本模块存在的理由：只 havoc 不证 = 把该分量移出验证范围（假绿方向），
        只证不 havoc = 拿未初始化的量做义务（伪 SAT，降级但难诊断）。两种都在
        这里当场炸掉。
        """
        bound = set(context.bound_components)
        proved = {goal.name for goal in relation_goals}
        declared = set(self._COMPONENTS)
        if bound != declared:
            raise AssertionError(
                "cutpoint havoc 未覆盖全部分量: "
                f"缺 {sorted(declared - bound)}, 多 {sorted(bound - declared)}"
            )
        if proved != declared:
            raise AssertionError(
                "cutpoint 证明义务未覆盖全部分量: "
                f"缺 {sorted(declared - proved)}, 多 {sorted(proved - declared)}"
            )


def _and_all(expressions: Iterable[object]):
    terms = [expr for expr in expressions]
    if not terms:
        return BoolVal(True)
    if len(terms) == 1:
        return terms[0]
    return And(*terms)


def _or_all(expressions: Iterable[object]):
    """空析取是 `False`：一个"没有任何合法取值"的集合必须拒绝一切状态，
    退化成 `True` 会让前提悄悄失效。"""
    terms = [expr for expr in expressions]
    if not terms:
        return BoolVal(False)
    if len(terms) == 1:
        return terms[0]
    return Or(*terms)
