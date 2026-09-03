"""CutpointRelationSchema 单元测试（docs/循环处理增强方案.md §4.1/§4.3）。

这些测试守的是一件事：**havoc 与证明义务必须覆盖同一组分量**。历史上三处
假绿缺口（host-gas 序号、lastGasCost、return data）全都是"只改 havoc 不改
证明目标"造成的，schema 的存在就是为了让那种改法当场炸掉。
"""

import pytest
from z3 import And, BitVecVal, Not, SolverFor, is_bv_value, sat, simplify, unsat

from state.host_gas import HOST_GAS_SEQ_KINDS
from state.smt_state import SMTState
from verification.cutpoint_relation import (
    CutpointRelationSchema,
    RelationContext,
    evm_memory_gas_cost,
    host_gas_seq_of,
)


def _solver(timeout_ms: int = 30000):
    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", timeout_ms)
    return solver


def _prove(conditions, state=None) -> bool:
    solver = _solver()
    if state is not None:
        for assumption in getattr(state, "assumptions", None) or []:
            solver.add(assumption)
    solver.add(Not(And(*conditions)))
    return solver.check() == unsat


class TestComponentSymmetry:
    """§4.3 的核心纪律：分量集合三方一致。"""

    def test_havoc_and_goals_cover_every_declared_component(self):
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=2, byte_offset_value=0x40)
        goals = schema.component_goals(
            context.state, context.state, 2, context=context
        )

        declared = set(schema.component_names)
        assert set(context.bound_components) == declared
        assert {goal.name for goal in goals} == declared

    @pytest.mark.parametrize(
        "dropped",
        ["host_gas_seq", "return_data_source", "gas", "memory_gas"],
    )
    def test_symmetry_guard_rejects_partially_bound_component(self, dropped):
        """只 havoc 不证（或反之）必须抛错，而不是静默放行。

        这四个分量是历史缺口的原型：它们在 build_havoc 里被 by construction
        耦合，若 goals 里没有对应义务，实际关系就从未被校验 —— 假绿方向。
        """
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=1, byte_offset_value=0x20)
        crippled = RelationContext(
            state=context.state,
            bound_components=tuple(
                name for name in context.bound_components if name != dropped
            ),
            memory_snapshot=context.memory_snapshot,
            stack_depth=1,
        )

        with pytest.raises(AssertionError, match=dropped):
            schema.component_goals(
                context.state, context.state, 1, context=crippled
            )

    def test_relation_holds_on_the_havoc_state_itself(self):
        """自耦合：havoc 产物对自己必须满足 R（否则 ② 的前提就不可满足）。"""
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=2, byte_offset_value=0x40)
        conditions = schema.goals(
            context.state, context.state, 2, context=context
        )
        assert _prove(conditions, context.state)


class TestEvolvingQuantitiesAreSymbolic:
    """跨轮次演化的量给具体常量 = 把定理钉死在初始轮（欠近似，假绿方向）。"""

    def test_host_gas_seq_is_havoced_to_fresh_symbols_not_zero(self):
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)

        for opcode in HOST_GAS_SEQ_KINDS:
            seq = host_gas_seq_of(context.state, opcode)
            assert not is_bv_value(simplify(seq)), (
                f"{opcode} 的调用序号被 havoc 成常量 {simplify(seq)}"
                " —— 归纳步只会证明「从第 0 次调用开始的一轮」"
            )

    def test_return_data_size_is_havoced_not_left_at_initial_zero(self):
        """`create_initial_state(return_data_size_bytes=0)` 的默认值不能沿用。

        循环**之前**若执行过 CALL，真实 size 非零；沿用 0 会把那片状态排除在
        定理适用域外，而 application 不会发现。
        """
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)

        size = context.state.callengine_return_data_size_bytes
        assert not is_bv_value(simplify(size))

        default_size = SMTState.create_initial_state(
            num_inputs=0
        ).callengine_return_data_size_bytes
        assert is_bv_value(simplify(default_size))  # 前提：默认确实是常量
        assert not size.eq(default_size)

    def test_memory_size_and_gas_are_symbolic(self):
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)

        assert not is_bv_value(simplify(context.state.evm_memory.MSize))
        assert not is_bv_value(simplify(context.state.evm_gas.Gas))


class TestGasIsRelational:
    """§4.1：gas 是 R 的内部控制流关系，不是单侧 envelope 假设。"""

    def test_gas_is_shared_across_both_sides_by_construction(self):
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        state = context.state

        assert _prove(
            [state.evm_gas.Gas == state.callengine_gas_remaining], state
        )

    def test_gas_goal_is_a_two_sided_equality(self):
        """gas 义务必须真的连接两侧，不能是恒真式。"""
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        other = schema.build_havoc(
            stack_depth=0, byte_offset_value=0, prefix="other"
        )

        gas_goal = next(
            goal
            for goal in schema.component_goals(
                context.state, other.state, 0, context=None
            )
            if goal.name == "gas"
        )
        solver = _solver()
        solver.add(Not(gas_goal.condition))
        assert solver.check() == sat, "两个独立 havoc 之间 gas 义务应可被违反"


class TestMemoryGasInvariant:
    """lastGasCost 与 MSize 的关系（§4.1）。"""

    def test_last_gas_cost_is_derived_from_memory_size(self):
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        state = context.state

        assert _prove(
            [
                state.callengine_memory_gas_used
                == evm_memory_gas_cost(state.callengine_memory_size_bytes)
            ],
            state,
        )

    def test_memory_gas_goal_requires_both_sides_and_the_derivation(self):
        """义务同时含「两侧相等」与「是 MSize 的函数」两条。

        只有两侧相等是健全性最低要求；缺了派生式，havoc 会把 lastGasCost 当
        完全自由的量，制造无谓降级。这里用两个独立 havoc 做语义检查——用同一个
        state 的话「两侧相等」会被 simplify 成恒真，什么也验不到。
        """
        from z3 import is_and

        schema = CutpointRelationSchema()
        left = schema.build_havoc(stack_depth=0, byte_offset_value=0, prefix="l")
        right = schema.build_havoc(stack_depth=0, byte_offset_value=0, prefix="r")
        goal = next(
            g
            for g in schema.component_goals(left.state, right.state, 0)
            if g.name == "memory_gas"
        )

        assert is_and(goal.condition)
        assert len(goal.condition.children()) == 2

        # (a) 两侧相等这一条真的连接两侧：独立 havoc 下义务可被违反
        solver = _solver()
        solver.add(Not(goal.condition))
        assert solver.check() == sat

        # (b) 派生式在场：x86 侧 lastGasCost 由 MSize 唯一确定。
        #     给定 MSize=64（2 words）⇒ lastGasCost = 2*3 + 4/512 = 6。
        solver = _solver()
        solver.add(goal.condition)
        solver.add(
            right.state.callengine_memory_size_bytes == BitVecVal(64, 64)
        )
        solver.add(
            right.state.callengine_memory_gas_used != BitVecVal(6, 64)
        )
        assert solver.check() == unsat, "派生式缺失：lastGasCost 未被 MSize 钉死"


class TestReturnDataIsNotTreatedAsReadonlyEnvironment:
    """return_data 可变，不能混在只读 environment 里（§4.1）。"""

    def test_readonly_environment_excludes_return_data(self):
        schema = CutpointRelationSchema()
        assert "return_data" in SMTState.ENVIRONMENT_FIELDS
        assert "return_data" not in schema._READONLY_ENVIRONMENT_FIELDS

    def test_return_data_source_goal_covers_content_size_and_pointer(self):
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        goal = next(
            g
            for g in schema.component_goals(
                context.state, context.state, 0, context=context
            )
            if g.name == "return_data_source"
        )
        rendered = str(goal.condition)
        assert "return_data" in rendered
        assert "return_data_size" in rendered
        assert "return_data_pointer" in rendered


class TestDomainPredicateReadsTheRightFieldPerSide:
    """域约束必须落在**该侧真正的** MSize 字段上（§4.4 ②）。

    两侧的"内存大小"在不同字段上:EVM 侧是语义字段 `evm_memory.MSize`
    (`evm_ir.semantics_gas.charge_dynamic_gas` 的唯一写入点),x86 侧是
    callEngine 镜像 `callengine_memory_size_bytes`。旧实现两侧都读镜像字段,
    于是 EVM 侧读到的永远是 havoc 原值——而域约束在 havoc 里已被 assume,
    该义务**恒真**。那不是"两侧都证过",是只证了一侧。
    """

    def _havoc_state(self):
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        return schema, context

    def test_evm_side_reads_the_semantic_msize_not_the_mirror(self):
        """把 EVM 侧 `evm_memory.MSize` 改成域外值,义务必须能被违反。

        读镜像字段时这条断言会失败(义务恒真)——那正是旧实现的缺口。
        """
        from z3 import BitVec

        _schema, context = self._havoc_state()
        state = context.state.copy()
        # 只动语义字段,镜像字段保持 havoc 原值:正是"EVM 侧扩容一轮"的样子。
        state.evm_memory.MSize = BitVec("escaped_msize", 64)

        solver = _solver()
        solver.add(Not(And(*context.domain_predicate(state, side="evm"))))
        assert solver.check() == sat, (
            "EVM 侧域义务读的不是 evm_memory.MSize —— 它恒真,等于没证"
        )

    def test_x86_side_reads_the_callengine_mirror(self):
        from z3 import BitVec

        _schema, context = self._havoc_state()
        state = context.state.copy()
        state.callengine_memory_size_bytes = BitVec("escaped_mirror", 64)

        solver = _solver()
        solver.add(Not(And(*context.domain_predicate(state, side="x86"))))
        assert solver.check() == sat

    def test_side_omitted_constrains_both_representations(self):
        """单参调用点看不出手里是哪一侧,谓词就得把两种表示都约束住。"""
        _schema, context = self._havoc_state()
        both = context.domain_predicate(context.state)
        evm_only = context.domain_predicate(context.state, side="evm")
        x86_only = context.domain_predicate(context.state, side="x86")
        assert len(both) == len(evm_only) + len(x86_only)

    def test_unknown_side_fails_hard(self):
        """站点名打错时必须当场炸,而不是悄悄退化成某一侧。"""
        _schema, context = self._havoc_state()
        with pytest.raises(ValueError):
            context.domain_predicate(context.state, side="EVM")


class TestDomainBoundIsTheProtocolCap:
    """域上界必须是**归纳闭合**的那个界(§4.4 ②:域内进、域内出)。"""

    def test_schema_cap_mirrors_the_interpreter_constant(self):
        """常量镜像自 `evm_ir/semantics_gas.py`,两处漂了必须当场红。"""
        from evm_ir.semantics_gas import _MEM_SIZE_CAP
        from verification.cutpoint_relation import EVM_MEMORY_SIZE_CAP

        assert EVM_MEMORY_SIZE_CAP == _MEM_SIZE_CAP
        assert CutpointRelationSchema().max_memory_size_bytes == _MEM_SIZE_CAP

    def test_protocol_cap_is_closed_under_one_expansion(self):
        """`requested ≤ cap`(非错误路径)⇒ 扩容后的 MSize 仍 ≤ cap 且 32 对齐。

        这就是把默认上界定在协议 cap 的依据:`calc_mem_size_64` 把
        `requested > cap` 分叉成 OUT_OF_GAS,所以未终止路径上 MSize 恒在界内。
        """
        from z3 import BitVec, BitVecVal, Solver, ULE

        from state.evm_gas_state import memory_expansion_fee
        from verification.cutpoint_relation import EVM_MEMORY_SIZE_CAP

        requested = BitVec("req", 64)
        mem_size = BitVec("msz", 64)
        last_gas = BitVec("lgc", 64)
        _fee, new_size, _new_lgc = memory_expansion_fee(
            mem_size, last_gas, requested
        )

        solver = Solver()
        solver.set("timeout", 30000)
        cap = BitVecVal(EVM_MEMORY_SIZE_CAP, 64)
        solver.add(ULE(mem_size, cap))                 # 域内进
        solver.add(mem_size & 0x1F == 0)
        solver.add(ULE(requested, cap))                # 非错误路径
        solver.add(Not(And(ULE(new_size, cap), new_size & 0x1F == 0)))
        assert solver.check() == unsat, "协议 cap 在一轮内存扩展下不闭合"

    def test_four_mib_bound_is_not_closed(self):
        """旧默认值 0x400000 不闭合——记录它被换掉的原因,别再换回去。

        一条 offset 为符号量的 MSTORE 就能把 MSize 顶到 4 MiB 以上,而
        `requested ≤ cap` 这条(路径上唯一真实存在的)约束拦不住它。
        """
        from z3 import BitVec, BitVecVal, Solver, ULE

        from state.evm_gas_state import memory_expansion_fee
        from verification.cutpoint_relation import EVM_MEMORY_SIZE_CAP

        requested = BitVec("req", 64)
        mem_size = BitVec("msz", 64)
        last_gas = BitVec("lgc", 64)
        _fee, new_size, _new_lgc = memory_expansion_fee(
            mem_size, last_gas, requested
        )

        solver = Solver()
        solver.set("timeout", 30000)
        four_mib = BitVecVal(0x400000, 64)
        solver.add(ULE(mem_size, four_mib))
        solver.add(mem_size & 0x1F == 0)
        solver.add(ULE(requested, BitVecVal(EVM_MEMORY_SIZE_CAP, 64)))
        solver.add(Not(ULE(new_size, four_mib)))
        assert solver.check() == sat, (
            "4 MiB 若真的闭合,换成协议 cap 的理由就不成立了"
        )


class TestMemoryGasCostDistributesOverIte:
    """`f(If(c,a,b)) ≡ If(c, f(a), f(b))` —— 纯语法改写,专治乘法里的 ITE。

    一轮循环体之后 MSize 的形状是 `If(expands, rounded, old)`。直接代进
    memoryGasCost 会把 ITE 埋进 `w*w` 的乘法内部,QF_BV eager bit-blast 要为
    "操作数是 ITE"的 64×64 乘法器建电路 —— CErc20 验收用例实测把
    `lastGasCost == memoryGasCost(MSize)` 从 0.3s 拖成 120s unknown。
    """

    def _ite_size(self):
        from z3 import Bool, BitVec, If

        return If(Bool("expands"), BitVec("rounded", 64), BitVec("old", 64))

    def test_distribution_preserves_semantics(self):
        """改写前后必须是同一个函数——这条一破,提速就变成了改语义。

        **逐支证**:`f(If(c,a,b)) == If(c,f(a),f(b))` 的证明本来就是对 c 分情况;
        而不分情况的那条查询恰恰是本改写要消除的难题(乘法操作数是 ITE),拿它
        当测试等于把待测缺陷写进测试(实测 30s unknown)。
        """
        from z3 import Bool

        from verification.cutpoint_relation import _memory_gas_cost_formula

        size = self._ite_size()
        expands = Bool("expands")
        for polarity in (expands, Not(expands)):
            solver = _solver()
            solver.add(polarity)
            solver.add(Not(evm_memory_gas_cost(size)
                           == _memory_gas_cost_formula(size)))
            assert solver.check() == unsat, f"分支 {polarity} 上语义被改了"

    def test_distribution_hoists_the_ite_above_the_multiplication(self):
        """顶层是 ITE、且两支内部各自不再含 ITE —— 乘法的操作数干净了。"""
        from z3 import Z3_OP_ITE, is_app_of

        result = evm_memory_gas_cost(self._ite_size())
        assert is_app_of(result, Z3_OP_ITE), "ITE 没被提到函数外"
        for branch in (result.arg(1), result.arg(2)):
            assert "If(" not in str(branch), f"分支里仍残留 ITE: {branch}"

    def test_plain_argument_is_unchanged(self):
        """非 ITE 参数走原路,不引入多余结构。"""
        from z3 import BitVec

        from verification.cutpoint_relation import _memory_gas_cost_formula

        size = BitVec("plain_size", 64)
        assert (
            str(simplify(evm_memory_gas_cost(size)))
            == str(simplify(_memory_gas_cost_formula(size)))
        )


class TestFingerprint:
    """证书缓存键必须随 R 的语义变化而变化。"""

    def test_fingerprint_is_stable_for_equal_schemas(self):
        assert (
            CutpointRelationSchema().fingerprint
            == CutpointRelationSchema().fingerprint
        )

    def test_fingerprint_tracks_component_set(self, monkeypatch):
        schema = CutpointRelationSchema()
        before = schema.fingerprint
        monkeypatch.setattr(
            CutpointRelationSchema,
            "_COMPONENTS",
            tuple(c for c in schema._COMPONENTS if c != "host_gas_seq"),
        )
        assert CutpointRelationSchema().fingerprint != before

    def test_fingerprint_tracks_host_gas_seq_kinds(self, monkeypatch):
        """序号语义随 HOST_GAS_SEQ_KINDS 增删而变，旧证书不能被新集合复用。"""
        before = CutpointRelationSchema().fingerprint
        monkeypatch.setattr(
            "verification.cutpoint_relation.HOST_GAS_SEQ_KINDS",
            frozenset(HOST_GAS_SEQ_KINDS | {"__SYNTHETIC__"}),
        )
        assert CutpointRelationSchema().fingerprint != before


class TestMemoryGasDerivationPremise:
    """`evm_memory_gas_cost` 用 `LShR(size, 5)` 的前提:size 总是 32 对齐。

    `state.evm_gas_state.memory_expansion_fee` 用的是 `LShR(requested+31, 5)`
    ——那里的输入是"本次访问触及的最高字节+1"(未对齐);而 schema 这边的输入
    是 `callengine_memory_size_bytes`,它是 **rounded** 值。两处口径不同但结果
    一致,前提就是"MSize 恒 32 对齐"。这条前提若在执行后被破坏,`memory_gas`
    分量就会在 latch/exit 处伪 SAT(降级)——甚至更糟,若两侧同时偏移则可能
    互相抵消而漏检。
    """

    def test_memory_size_stays_32_aligned_across_expansion(self):
        from z3 import BitVec, Not, Solver, unsat

        from state.evm_gas_state import memory_expansion_fee

        requested = BitVec("req", 64)
        mem_size = BitVec("msz", 64)
        last_gas = BitVec("lgc", 64)
        _fee, new_size, _new_lgc = memory_expansion_fee(
            mem_size, last_gas, requested
        )

        solver = Solver()
        solver.set("timeout", 30000)
        solver.add(mem_size & 0x1F == 0)          # 输入对齐
        solver.add(Not(new_size & 0x1F == 0))     # 输出不对齐?
        assert solver.check() == unsat, "内存扩展后 MSize 不再 32 对齐"

    def test_last_gas_cost_tracks_memory_gas_cost_of_memory_size(self):
        """`lastGasCost == memoryGasCost(MSize)` 是被扩展路径保持的不变式。

        这正是 schema 的 `memory_gas` 分量除"两侧相等"外还断言的那一条。它成立,
        havoc 才能不把 lastGasCost 当完全自由的量(否则只能过近似 ⇒ 无谓降级)。
        """
        from z3 import BitVec, BitVecVal, LShR, Not, Solver, UGT, ULE, unsat

        from state.evm_gas_state import memory_expansion_fee
        from verification.cutpoint_relation import evm_memory_gas_cost

        requested = BitVec("req", 64)
        mem_size = BitVec("msz", 64)
        last_gas = BitVec("lgc", 64)
        _fee, new_size, new_last_gas = memory_expansion_fee(
            mem_size, last_gas, requested
        )

        solver = Solver()
        solver.set("timeout", 60000)
        solver.add(ULE(requested, BitVecVal(0x1FFFFFFFE0, 64)))   # cap 内
        solver.add(UGT(LShR(requested + 31, 5) << 5, mem_size))    # 确实扩展
        solver.add(Not(new_last_gas == evm_memory_gas_cost(new_size)))
        assert solver.check() == unsat, (
            "扩展后 lastGasCost 与 memoryGasCost(MSize) 脱钩"
        )


class TestHostGasSeqComponent:
    """host-gas 调用序号分量的两个方向。"""

    def test_havoc_covers_every_sequenced_opcode(self):
        """必须覆盖 `HOST_GAS_SEQ_KINDS` 全部键。

        漏掉任何一个,`next_host_gas_seq` 缺键就默认 `BitVecVal(0, 256)`——那是
        具体常量,会把定理钉死在"从第 0 次调用开始",属假绿方向。
        """
        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        missing = [
            op for op in HOST_GAS_SEQ_KINDS
            if op not in context.state.host_gas_seq
        ]
        assert missing == [], f"这些 opcode 的序号没被 havoc: {missing}"

    def test_one_sided_extra_host_call_is_caught(self):
        """一侧多执行一次 host 调用 ⇒ 序号义务不可满足(被抓住)。

        这正是序号机制要抓的:两侧 host 调用序列在数量或次序上偏移时,UF 不再
        相消。方向是降级(inconclusive)而非假绿。
        """
        from z3 import Not, Solver, sat, unsat

        from state.host_gas import next_host_gas_seq

        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        left, right = context.state.copy(), context.state.copy()
        next_host_gas_seq(left, "SLOAD")          # 只有一侧调用

        goal = next(
            g for g in schema.component_goals(left, right, 0)
            if g.name == "host_gas_seq"
        )
        solver = Solver()
        solver.add(goal.condition)
        assert solver.check() == unsat, "单侧多一次 host 调用没被序号分量抓住"

        # 且义务本身不是恒真(否则什么也没验到)
        solver = Solver()
        solver.add(Not(goal.condition))
        assert solver.check() == sat


class TestModelRangeErrorIsDistinct:
    """建模范围错误必须是**专用异常**，不能靠裸 `except ValueError` 捕获。

    深度类合法但超出 schema 范围时应当降级为 inconclusive；而裸捕获
    `ValueError` 会连带吞掉别处真正该 fail-hard 的编程错误，把 bug 伪装成
    「这个循环证不了」——那是最难查的一类问题。
    """

    def test_out_of_range_depth_raises_the_dedicated_error(self):
        from verification.cutpoint_relation import CutpointModelRangeError

        schema = CutpointRelationSchema()
        with pytest.raises(CutpointModelRangeError, match="exceeds the schema bound"):
            schema.build_havoc(stack_depth=513)      # 513*0x20 = 0x4020 > 0x4000

    def test_mismatched_byte_offset_also_uses_it(self):
        from verification.cutpoint_relation import CutpointModelRangeError

        schema = CutpointRelationSchema()
        with pytest.raises(CutpointModelRangeError, match="absolute depth class"):
            schema.build_havoc(stack_depth=1, byte_offset_value=0x40)

    def test_it_is_a_valueerror_subclass_for_compatibility(self):
        from verification.cutpoint_relation import CutpointModelRangeError

        assert issubclass(CutpointModelRangeError, ValueError)


class TestPersistentInvariantsAppearInGoals:
    """schema 的 `persistent_invariants` 必须进 R 的证明目标。

    `Tier1LoopInduction._invariant_premises` 把它们当**前提**，若 `goals()` 里
    没有对应义务，就是白嫖（定理凭空更强）。这条测试固化前提/义务的配对。
    """

    def test_goals_include_persistent_invariants(self):
        from z3 import BitVecVal

        marker = BitVecVal(0xC0FFEE, 64)

        def _marker_invariant(evm_state, x86_state):
            return [evm_state.callengine_stack_base != marker]

        schema = CutpointRelationSchema(
            persistent_invariants=[_marker_invariant]
        )
        context = schema.build_havoc(stack_depth=0, byte_offset_value=0)
        conditions = schema.goals(
            context.state, context.state, 0, context=context
        )
        rendered = " ".join(str(c) for c in conditions)
        assert "12648430" in rendered or "0xc0ffee" in rendered.lower(), (
            "persistent_invariants 没有出现在 R 的证明目标里——"
            "把它当前提就是白嫖"
        )

# ---------------------------------------------------------------------------
# 验收基准 11:CALLENGINE side-channel 属性 ↔ limb 镜像(§4.5.5)
# ---------------------------------------------------------------------------

class TestCallengineMirrorClosure:
    """`R` 必须拒绝"属性相等、`[R13+off]` limb 陈旧"的状态。

    这是 §4.5.5 记录的那个**已实测**的假绿缺口的哨兵。x86 侧读 callEngine 字段
    走 side-channel 快路径直接取属性,limb 只是宽度不符时回退内存读用的镜像;
    `build_havoc` 通过 `_sync_callengine` 两边同步写,但证明义务一度只比属性,
    于是定理在"属性 == limb"的状态上证出、却可以被应用到 limb 陈旧的状态
    ——定理被用到证明域之外。

    修复前实测:6 个镜像字段**全部**接受陈旧 limb(`sat`)。
    """

    @pytest.mark.parametrize(
        "attr,offset_name",
        CutpointRelationSchema._CALLENGINE_MIRROR_FIELDS,
        ids=[name for _attr, name in
             CutpointRelationSchema._CALLENGINE_MIRROR_FIELDS],
    )
    def test_stale_limb_is_rejected(self, attr, offset_name):
        from state.x86_state import MemoryDomain
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE
        from x86_64.models import Register
        from z3 import BitVec

        schema = CutpointRelationSchema()
        context = schema.build_havoc(stack_depth=1)
        evm_state = context.state.copy()
        x86_state = context.state.copy()

        # 只改 x86 侧的 limb,属性保持不动 —— 正是"两者分叉"那一幕。
        r13 = x86_state.x86_registers.get_register(Register.R13)
        offset = GO_HPC_EVM_PROFILE.offsets[offset_name]
        tampered = BitVec(f"tampered_{offset_name}", 64)
        x86_state.x86_memory = x86_state.x86_memory.store_limb(
            r13 + BitVecVal(offset, 64), tampered,
            domain=MemoryDomain.CALLENGINE,
        )

        solver = _solver()
        for constraint in context.domain_constraints:
            solver.add(constraint)
        for condition in schema.goals(
            evm_state, x86_state, 1, memory_snapshot=context.memory_snapshot
        ):
            solver.add(condition)
        # "R 成立 **且** limb 与属性不同"必须不可满足。
        solver.add(tampered != getattr(x86_state, attr))

        assert solver.check() == unsat, (
            f"R 接受了 {offset_name} 的陈旧 limb —— 定理会被应用到它证明域之外的"
            "状态上(§4.5.5 的假绿缺口)"
        )

    def test_mirror_field_list_matches_what_havoc_syncs(self):
        """字段清单是义务来源,漏一个就是"分量名在、义务里没有"的内部缺口。

        `build_havoc` 自己会对账并抛错,这里从**外部**再钉一次:清单非空,
        且每个字段名在 profile offsets 里确实存在(拼错会让对账形同虚设)。
        """
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE

        fields = CutpointRelationSchema._CALLENGINE_MIRROR_FIELDS
        assert fields, "镜像字段清单为空 ⇒ callengine_mirror 分量没有任何义务"
        for attr, offset_name in fields:
            assert offset_name in GO_HPC_EVM_PROFILE.offsets, (
                f"{offset_name} 不在 AOT profile 的 offsets 里"
            )
            assert hasattr(SMTState.create_initial_state(), attr), (
                f"{attr} 不是 SMTState 的字段"
            )
