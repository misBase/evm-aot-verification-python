"""
x86-64 符号执行引擎（参考 evm_ir）。

定义 X86SymbolicExecutor 类，实现 worklist 驱动的符号执行。
"""

from typing import List, Dict, Optional, Tuple, Set
from z3 import BitVecVal, Not, And, Or, If, Solver, simplify, unsat

from .aot_profile import GO_HPC_EVM_PROFILE
from .models import Register, X86Block, X86Instruction
from .cfg_structures import X86DynamicCFG, X86EdgeType
from .cfg_state import X86GlobalState, X86WorldState, X86Constraints
from .cfg_strategies import X86DFSStrategy, X86TopologicalStrategy
from .disassembler import parse_operands
from state.smt_state import SMTState


class X86SymbolicExecutor:
    """基于 worklist 的 x86-64 符号执行引擎。

    完全参考 evm_ir 的设计：
    - work_list 管理待执行状态
    - 动态构建 CFG
    - 策略模式控制搜索顺序
    - 可达性检查剪枝不可达状态
    """

    GO_HOST_NODE_BASE_ADDR = 0x7FFFFFFFFFFF0000
    # 兼容旧测试/调用方：第一个 GO_HOST 节点地址
    GO_HOST_NODE_ADDR = GO_HOST_NODE_BASE_ADDR

    def __init__(self,
                 blocks: List[X86Block],
                 strategy_cls: type = X86DFSStrategy,
                 max_depth: int = 100,
                 use_reachability_check: bool = True,
                 enable_go_bridge: bool = True,
                 enable_merge: bool = True):
        """初始化符号执行引擎。

        Args:
            blocks: 所有 x86-64 块列表
            strategy_cls: 搜索策略类
            max_depth: 最大执行深度
            use_reachability_check: 是否使用可达性检查
            enable_go_bridge: 是否启用 ret -> GO_HOST -> returnAddress 建模
            enable_merge: 是否启用合流点合并优化
        """
        self.blocks = blocks
        self.blocks_by_addr: Dict[int, X86Block] = {block.start_addr: block for block in blocks}
        self.block_index: Dict[int, int] = {block.start_addr: i for i, block in enumerate(blocks)}
        self.max_depth = max_depth
        self.use_reachability_check = use_reachability_check
        self.enable_go_bridge = enable_go_bridge
        self.enable_merge = enable_merge
        self.aot_profile = GO_HPC_EVM_PROFILE

        # 创建动态 CFG
        self.cfg = X86DynamicCFG(blocks)

        # work_list：待执行的全局状态列表
        self.work_list: List[X86GlobalState] = []

        # 合流点合并优化
        if enable_merge:
            topo_order = self._compute_topological_order()
            self.merge_points: Dict[int, int] = self._compute_static_merge_points(topo_order)
            self.merge_buffers: Dict[int, List[X86GlobalState]] = {}
            self.strategy = X86TopologicalStrategy(self.work_list, max_depth, topo_order)
        else:
            self.merge_points = {}
            self.merge_buffers = {}
            # 创建搜索策略
            self.strategy = strategy_cls(self.work_list, max_depth)

        # 统计信息
        self.total_states = 0
        self.pruned_states = 0

        # 终止状态列表
        self.final_states: List[X86GlobalState] = []

        # 每个 CallGoFunction-ret 站点对应一个独立 GO_HOST 外部节点
        self._go_host_addr_by_ret_block: Dict[int, int] = {}

    def _get_static_successors(self, block_idx: int, block: X86Block) -> List[int]:
        """解析 block 末尾指令，返回后继 block 地址列表（静态分析）。

        Args:
            block_idx: block 在 self.blocks 中的索引
            block: 当前 block

        Returns:
            后继 block 地址列表
        """
        successors = []
        if not block.instructions:
            # 空块 fallthrough
            if block_idx + 1 < len(self.blocks):
                successors.append(self.blocks[block_idx + 1].start_addr)
            return successors

        last_insn = block.instructions[-1]
        mnemonic = last_insn.mnemonic.lower()

        if mnemonic == 'jmp':
            operands = parse_operands(last_insn)
            target_addr = operands.get('jump_target')
            if target_addr is not None and target_addr in self.blocks_by_addr:
                successors.append(target_addr)

        elif mnemonic in ['jb', 'jae', 'ja', 'jbe', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            # Jcc: 跳转目标 + fallthrough
            operands = parse_operands(last_insn)
            target_addr = operands.get('jump_target')
            if target_addr is not None and target_addr in self.blocks_by_addr:
                successors.append(target_addr)
            if block_idx + 1 < len(self.blocks):
                successors.append(self.blocks[block_idx + 1].start_addr)

        elif mnemonic == 'ret':
            # ret: 对于 go bridge 情况，后继在运行时确定，静态无法判断
            # 保守处理：不添加后继
            pass

        else:
            # fallthrough
            if block_idx + 1 < len(self.blocks):
                successors.append(self.blocks[block_idx + 1].start_addr)

        return successors

    def _compute_static_merge_points(self, topo_order: Dict[int, int] = None) -> Dict[int, int]:
        """计算静态合流点：入边数 >= 2 的 block（排除回边）。

        Args:
            topo_order: 拓扑序映射，若提供则跳过回边（src_order >= dst_order 的边）

        Returns:
            {block_addr: incoming_count}，仅包含前向入边 >= 2 的 block
        """
        incoming: Dict[int, int] = {}
        for i, block in enumerate(self.blocks):
            src_addr = block.start_addr
            for succ_addr in self._get_static_successors(i, block):
                if topo_order is not None:
                    src_order = topo_order.get(src_addr, float('inf'))
                    dst_order = topo_order.get(succ_addr, float('inf'))
                    if src_order >= dst_order:
                        continue  # 跳过回边
                incoming[succ_addr] = incoming.get(succ_addr, 0) + 1
        return {addr: cnt for addr, cnt in incoming.items() if cnt >= 2}

    def _compute_topological_order(self) -> Dict[int, int]:
        """使用 Kahn 算法计算拓扑序。

        Returns:
            {block_addr: 拓扑序号} 映射
        """
        # 构建邻接表和入度
        adj: Dict[int, List[int]] = {block.start_addr: [] for block in self.blocks}
        in_degree: Dict[int, int] = {block.start_addr: 0 for block in self.blocks}

        for i, block in enumerate(self.blocks):
            for succ_addr in self._get_static_successors(i, block):
                if succ_addr in adj:
                    adj[block.start_addr].append(succ_addr)
                    in_degree[succ_addr] = in_degree.get(succ_addr, 0) + 1

        # Kahn 算法
        from collections import deque
        queue = deque()
        for addr, deg in in_degree.items():
            if deg == 0:
                queue.append(addr)

        topo_order: Dict[int, int] = {}
        order = 0
        while queue:
            addr = queue.popleft()
            topo_order[addr] = order
            order += 1
            for succ_addr in adj.get(addr, []):
                in_degree[succ_addr] -= 1
                if in_degree[succ_addr] == 0:
                    queue.append(succ_addr)

        # 未被排序的节点（循环中的）赋予最大序号
        for block in self.blocks:
            if block.start_addr not in topo_order:
                topo_order[block.start_addr] = order
                order += 1

        return topo_order

    def _merge_at_confluence(self, addr: int, states: List[X86GlobalState]) -> X86GlobalState:
        """在合流点合并多条路径的状态。

        使用 If(path_condition, val_from_A, val_from_B) 合并每个字段。

        Args:
            addr: 合流点 block 地址
            states: 到达此合流点的所有状态

        Returns:
            合并后的 X86GlobalState
        """
        if len(states) == 1:
            return states[0]

        # 创建合并后的 mstate
        merged_mstate = SMTState._create_empty()

        # 合并寄存器
        all_regs: Set[str] = set()
        for s in states:
            all_regs.update(s.mstate.x86_registers._registers.keys())

        from state.smt_state import X86RegisterState
        merged_regs = X86RegisterState()
        for reg in all_regs:
            # 从最后一个状态开始作为默认值，逆序用 If 叠加
            expr = states[-1].mstate.x86_registers._registers.get(reg, BitVecVal(0, 64))
            for s in reversed(states[:-1]):
                cond = s.get_constraints().as_bool()
                s_val = s.mstate.x86_registers._registers.get(reg, BitVecVal(0, 64))
                expr = If(cond, s_val, expr)
            merged_regs._registers[reg] = expr
        merged_mstate.x86_registers = merged_regs

        # 合并标志位
        all_flags: Set[str] = set()
        for s in states:
            all_flags.update(s.mstate.x86_registers._flags.keys())
        for flag in all_flags:
            expr = states[-1].mstate.x86_registers.get_flag(flag)
            for s in reversed(states[:-1]):
                cond = s.get_constraints().as_bool()
                expr = If(cond, s.mstate.x86_registers.get_flag(flag), expr)
            merged_regs._flags[flag] = expr

        # 合并 x86 内存（Array 级 If）
        from state.smt_state import X86MemoryState
        expr = states[-1].mstate.x86_memory.Memory
        for s in reversed(states[:-1]):
            cond = s.get_constraints().as_bool()
            expr = If(cond, s.mstate.x86_memory.Memory, expr)
        merged_mstate.x86_memory = X86MemoryState(memory_array=expr)

        # 合并 return_offset, return_length
        offset_expr = states[-1].mstate.return_offset
        length_expr = states[-1].mstate.return_length
        for s in reversed(states[:-1]):
            cond = s.get_constraints().as_bool()
            offset_expr = If(cond, s.mstate.return_offset, offset_expr)
            length_expr = If(cond, s.mstate.return_length, length_expr)
        merged_mstate.return_offset = offset_expr
        merged_mstate.return_length = length_expr

        # EVM 状态直接从第一个状态复制（x86 执行不修改 EVM 状态）
        merged_mstate.evm_stack = states[0].mstate.evm_stack
        merged_mstate.evm_memory = states[0].mstate.evm_memory
        merged_mstate.evm_storage = states[0].mstate.evm_storage
        merged_mstate.evm_gas = states[0].mstate.evm_gas
        merged_mstate.pc = states[0].mstate.pc

        # 环境信息共享
        merged_mstate.calldata = states[0].mstate.calldata
        merged_mstate.calldatasize = states[0].mstate.calldatasize
        merged_mstate.callvalue = states[0].mstate.callvalue
        merged_mstate.basefee = states[0].mstate.basefee

        # 合并约束 = Or(所有原路径条件)
        merged_world = X86WorldState()
        conditions = [s.get_constraints().as_bool() for s in states]
        merged_world.constraints.add(Or(*conditions))

        merged_node = self.cfg.get_or_create_node(addr)
        result = X86GlobalState(mstate=merged_mstate, world_state=merged_world, node=merged_node)
        result.depth = max(s.depth for s in states)
        return result

    def manage_cfg(self, insn: X86Instruction, new_states: List[X86GlobalState],
                   from_addr: int) -> None:
        """管理 CFG 构建。

        在执行过程中动态添加边。

        Args:
            insn: 当前执行的指令
            new_states: 新生成的状态列表
            from_addr: 前驱节点地址（当前块地址）
        """
        if not new_states:
            return

        mnemonic = insn.mnemonic.lower()

        if mnemonic == 'jmp':
            # 无条件跳转：添加单条边
            if len(new_states) == 1 and new_states[0].node:
                to_addr = new_states[0].node.address
                self.cfg.add_edge(from_addr, to_addr, X86EdgeType.UNCONDITIONAL,
                                source_instruction=insn)

        elif mnemonic in ['jb', 'jae', 'ja', 'jbe', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            # 条件跳转：优先按真实跳转目标判定边类型，避免剪枝后仅剩一支时类型错标
            target_addr = parse_operands(insn).get('jump_target')
            for i, state in enumerate(new_states):
                if not state.node:
                    continue
                to_addr = state.node.address

                if target_addr is not None and to_addr == target_addr:
                    edge_type = X86EdgeType.CONDITIONAL_TRUE
                    condition = self._extract_jcc_condition(state)
                else:
                    # 兜底：无法解析目标时退回顺序约定（第一个为 true）
                    if target_addr is None and i == 0:
                        edge_type = X86EdgeType.CONDITIONAL_TRUE
                        condition = self._extract_jcc_condition(state)
                    else:
                        edge_type = X86EdgeType.CONDITIONAL_FALSE
                        condition = None  # fallthrough 条件是跳转条件的否定，在边类型中体现

                self.cfg.add_edge(from_addr, to_addr, edge_type, condition,
                                source_instruction=insn)
        elif mnemonic == 'ret':
            # ret 的 GO 往返边在 _handle_ret_with_go_bridge 中按实际执行动态添加
            return

        else:
            # Fallthrough：添加顺序执行边
            if len(new_states) == 1 and new_states[0].node:
                to_addr = new_states[0].node.address
                self.cfg.add_edge(from_addr, to_addr, X86EdgeType.FALLTHROUGH,
                                source_instruction=insn)

    def execute(self, initial_state: SMTState, entry_addr: Optional[int] = None) -> List[X86GlobalState]:
        """执行符号执行。

        Args:
            initial_state: 初始机器状态
            entry_addr: 入口块地址（默认为第一个块）

        Returns:
            所有终止状态列表
        """
        # 确定入口点
        if entry_addr is None:
            if not self.blocks:
                raise ValueError("No blocks to execute")
            entry_addr = self.blocks[0].start_addr

        entry_block = self.blocks_by_addr.get(entry_addr)
        if entry_block is None:
            raise ValueError(f"Entry block not found: addr=0x{entry_addr:x}")

        # 创建初始全局状态
        entry_node = self.cfg.get_or_create_node(entry_addr)
        initial_global_state = X86GlobalState(
            mstate=initial_state,
            node=entry_node
        )
        initial_global_state.depth = 0

        # 添加到 work_list
        self.work_list.append(initial_global_state)

        # 主执行循环
        for global_state in self.strategy:
            # 合流点合并检测
            if self.enable_merge:
                addr = global_state.node.address if global_state.node else None
                if addr is not None and addr in self.merge_points:
                    buf = self.merge_buffers.setdefault(addr, [])
                    buf.append(global_state)
                    if len(buf) < self.merge_points[addr]:
                        continue  # 等待其他路径到达
                    # 所有路径已到达，合并
                    global_state = self._merge_at_confluence(addr, buf)
                    del self.merge_buffers[addr]

            # 循环检测调用点（TODO: 实现检测逻辑）
            self._detect_and_handle_loops(global_state)

            # 执行单个状态
            new_states = self.execute_state(global_state)

            if new_states:
                # 可达性检查和剪枝
                if self.use_reachability_check and len(new_states) > 1:
                    old_count = len(new_states)
                    new_states = [
                        state for state in new_states
                        if state.get_constraints().is_possible()
                    ]
                    pruned = old_count - len(new_states)
                    self.pruned_states += pruned

                # 更新 CFG
                if global_state.node and global_state.node.block.instructions:
                    last_insn = global_state.node.block.instructions[-1]
                    from_addr = global_state.node.address
                    self.manage_cfg(last_insn, new_states, from_addr)

                # 添加新状态到 work_list
                self.work_list.extend(new_states)
                self.total_states += len(new_states)

            # 如果是终止状态，保存
            if self._is_terminal_state(global_state):
                self.final_states.append(global_state)

        # flush 残余 merge buffer（某些路径被剪枝导致入边不齐）
        if self.enable_merge:
            self._flush_merge_buffers()

        return self.final_states

    def _flush_merge_buffers(self) -> None:
        """处理残余的合流 buffer（某些路径被可达性剪枝导致入边不齐）。"""
        while self.merge_buffers:
            for addr in list(self.merge_buffers.keys()):
                buf = self.merge_buffers.pop(addr)
                if not buf:
                    continue
                merged = self._merge_at_confluence(addr, buf)

                self._detect_and_handle_loops(merged)
                new_states = self.execute_state(merged)

                if new_states:
                    if self.use_reachability_check and len(new_states) > 1:
                        new_states = [
                            state for state in new_states
                            if state.get_constraints().is_possible()
                        ]
                    if merged.node and merged.node.block.instructions:
                        last_insn = merged.node.block.instructions[-1]
                        self.manage_cfg(last_insn, new_states, merged.node.address)

                    # 新状态可能又到达合流点，或需要继续执行
                    for ns in new_states:
                        ns_addr = ns.node.address if ns.node else None
                        if ns_addr is not None and ns_addr in self.merge_points:
                            buf2 = self.merge_buffers.setdefault(ns_addr, [])
                            buf2.append(ns)
                        elif self._is_terminal_state(ns):
                            self.final_states.append(ns)
                        else:
                            # 非合流点非终止：继续执行，结果重新派发
                            self._flush_execute_state(ns)

                if self._is_terminal_state(merged):
                    self.final_states.append(merged)

    def _flush_execute_state(self, state: X86GlobalState) -> None:
        """在 flush 阶段继续执行单个非终止、非合流点状态，并将结果正确派发。

        递归执行直到状态到达合流点（加入 merge_buffers）或终止（加入 final_states）。
        depth >= max_depth 时停止递归，防止无限循环。
        """
        if state.depth >= self.max_depth:
            return

        self._detect_and_handle_loops(state)
        new_states = self.execute_state(state)

        if new_states:
            if self.use_reachability_check and len(new_states) > 1:
                new_states = [
                    ns for ns in new_states
                    if ns.get_constraints().is_possible()
                ]
            if state.node and state.node.block.instructions:
                last_insn = state.node.block.instructions[-1]
                self.manage_cfg(last_insn, new_states, state.node.address)

            for ns in new_states:
                ns_addr = ns.node.address if ns.node else None
                if ns_addr is not None and ns_addr in self.merge_points:
                    buf2 = self.merge_buffers.setdefault(ns_addr, [])
                    buf2.append(ns)
                elif self._is_terminal_state(ns):
                    self.final_states.append(ns)
                else:
                    self._flush_execute_state(ns)

        if self._is_terminal_state(state):
            self.final_states.append(state)

    def execute_state(self, global_state: X86GlobalState) -> List[X86GlobalState]:
        """执行单个全局状态。

        Args:
            global_state: 要执行的全局状态

        Returns:
            新生成的全局状态列表
        """
        node = global_state.node
        if node is None:
            return []

        # 将当前状态添加到节点的状态列表（用于追踪和调试）
        node.states.append(global_state)

        block = node.block
        mstate = global_state.mstate

        # 执行块中的所有指令
        new_mstate = mstate.copy()

        for insn in block.instructions:
            new_mstate = insn.to_z3(new_mstate)

        # 持久化块执行后的机器状态，供终止判定与结果合并使用
        global_state.mstate = new_mstate

        # 获取最后一条指令来确定控制流
        if not block.instructions:
            # 空块，顺序执行到下一个块
            return self._handle_fallthrough(global_state, new_mstate, block)

        last_insn = block.instructions[-1]
        mnemonic = last_insn.mnemonic.lower()

        if mnemonic == 'jmp':
            return self._handle_jmp(global_state, new_mstate, block, last_insn)
        elif mnemonic in ['jb', 'jae', 'ja', 'jbe', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            return self._handle_jcc(global_state, new_mstate, block, last_insn)
        elif mnemonic == 'ret':
            return self._handle_ret_with_go_bridge(global_state, new_mstate, block, last_insn)
        else:
            # 顺序执行到下一个块
            return self._handle_fallthrough(global_state, new_mstate, block)

    def _handle_jmp(self, global_state: X86GlobalState, mstate: SMTState,
                    block: X86Block, insn: X86Instruction) -> List[X86GlobalState]:
        """处理 JMP 指令。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块
            insn: JMP 指令

        Returns:
            新全局状态列表

        Note:
            根据编译器实现，机器码中没有间接跳转，
            所有跳转目标都是静态确定的。
        """
        import copy as copy_module

        # 解析跳转目标
        operands = parse_operands(insn)

        target_addr = operands.get('jump_target')
        
        if target_addr is None:
            # 无法解析目标，可能是间接跳转或解析错误
            # 检查是否是明确的间接跳转（寄存器/内存跳转）
            if operands.get('is_indirect'):
                from utils.exceptions import UnsupportedJumpError
                raise UnsupportedJumpError(
                    "indirect_jump",
                    f"Indirect JMP at address 0x{insn.addr:x}",
                    "x86 indirect jumps are not supported by the compiler"
                )
            # 否则返回空列表（可能是解析失败或外部目标）
            return []

        # 直接跳转（静态目标）
        target_block = self.blocks_by_addr.get(target_addr)

        if target_block is None:
            # 目标块不存在，可能是外部跳转或超出范围
            return []

        target_node = self.cfg.get_or_create_node(target_addr)
        new_state = X86GlobalState(
            mstate=mstate,
            world_state=copy_module.copy(global_state.world_state),  # 单路径使用 copy（参考 mythril）
            node=target_node
        )
        new_state.depth = global_state.depth + 1
        return [new_state]

    def _handle_jcc(self, global_state: X86GlobalState, mstate: SMTState,
                    block: X86Block, insn: X86Instruction) -> List[X86GlobalState]:
        """处理条件跳转指令（Jcc）。

        支持的条件跳转指令：
        - JE/JNE: 等于/不等于
        - JB/JAE: 无符号小于/大于等于
        - JA/JBE: 无符号大于/小于等于
        - JL/JGE: 有符号小于/大于等于
        - JLE/JG: 有符号小于等于/大于

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块
            insn: Jcc 指令

        Returns:
            新全局状态列表（两个分支）

        Note:
            根据编译器实现：
            - 所有跳转目标都是静态确定的
            - 没有间接跳转
        """
        import copy as copy_module

        # 解析跳转目标
        operands = parse_operands(insn)
        target_addr = operands.get('jump_target')
        
        # 检测间接跳转（真正的间接寻址）
        if target_addr is None:
            # 检查是否是明确的间接跳转
            if operands.get('is_indirect'):
                from utils.exceptions import UnsupportedJumpError
                raise UnsupportedJumpError(
                    "indirect_conditional_jump",
                    f"Indirect conditional jump at address 0x{insn.addr:x}",
                    "x86 indirect conditional jumps are not supported by the compiler"
                )
            # 如果只是解析失败，目标块设为 None（后续处理会跳过该分支）
        
        target_block = self.blocks_by_addr.get(target_addr) if target_addr else None

        mnemonic = insn.mnemonic.lower()

        # 构建跳转条件
        # 注意：当前实现使用符号变量作为占位符
        # 完整实现需要从 CPU 标志寄存器（CF, ZF, SF, OF）中提取条件
        jump_condition = self._build_jump_condition(mnemonic, mstate)
        fallthrough_condition = Not(jump_condition)

        new_states = []

        # 分支 1：跳转到目标（条件为真）
        if target_block is not None:
            target_node = self.cfg.get_or_create_node(target_addr)

            # 浅拷贝状态（X86WorldState.__copy__ 已正确实现）
            jump_world_state = copy_module.copy(global_state.world_state)
            jump_world_state.constraints.add(jump_condition)

            jump_state = X86GlobalState(
                mstate=mstate.copy(),
                world_state=jump_world_state,
                node=target_node
            )
            jump_state.depth = global_state.depth + 1
            new_states.append(jump_state)

        # 分支 2：顺序执行（条件为假）
        current_idx = self.block_index[block.start_addr]
        if current_idx + 1 < len(self.blocks):
            fallthrough_addr = self.blocks[current_idx + 1].start_addr
            fallthrough_node = self.cfg.get_or_create_node(fallthrough_addr)

            # 浅拷贝状态（X86WorldState.__copy__ 已正确实现）
            fallthrough_world_state = copy_module.copy(global_state.world_state)
            fallthrough_world_state.constraints.add(fallthrough_condition)

            fallthrough_state = X86GlobalState(
                mstate=mstate.copy(),
                world_state=fallthrough_world_state,
                node=fallthrough_node
            )
            fallthrough_state.depth = global_state.depth + 1
            new_states.append(fallthrough_state)

        return new_states

    def _is_call_go_function_pattern(self, block: X86Block) -> bool:
        """识别 ret 块是否匹配 CallGoFunction 模式。

        根据 go-hpc-evm 编译器的 compileCallGoFunction 函数，序列为：
          1. ... (可选：lea/ mov 准备返回地址到寄存器)
          2. mov [r13+0xf0], reg/imm   ; 写 return_address
          3. mov [r13+0xe0], imm       ; 写 status_code
          4. mov [r13+0x28], imm       ; 写 stack_pointer (可能省略)
          5. ret                       ; 返回 Go runtime

        支持两种模式：
        - 完整模式（5条）：ret 前有 stack_pointer 写入
        - 简化模式（3-4条）：ret 前无 stack_pointer 写入（用于测试）
        """
        if not self.enable_go_bridge:
            return False

        insns = block.instructions
        if len(insns) < 3:
            return False

        # 检查末尾必须是 ret
        if insns[-1].mnemonic.lower() != 'ret':
            return False

        profile_offsets = self.aot_profile.offsets
        ret_addr_offset = profile_offsets["return_address"]
        status_offset = profile_offsets["status_code"]
        stack_ptr_offset = profile_offsets["stack_pointer"]

        # 从 ret 往前检查，找关键指令
        # 倒数第1条是 ret，从倒数第2条开始找
        status_insn = None
        ret_addr_insn = None
        sp_insn = None

        # 从倒数第2条开始往前找
        for i in range(len(insns) - 2, -1, -1):
            insn = insns[i]
            if not insn.mnemonic.lower().startswith("mov"):
                continue
            if not self._is_mov_to_r13_offset(insn, ret_addr_offset):
                continue

            # 找到了写 return_address 的指令
            ret_addr_insn = insn
            ret_addr_idx = i

            # 检查它后面是否有写 status_code 和 stack_pointer
            for j in range(i + 1, len(insns) - 1):  # 不包括最后的 ret
                next_insn = insns[j]
                if not next_insn.mnemonic.lower().startswith("mov"):
                    continue
                if status_insn is None and self._is_mov_to_r13_offset(next_insn, status_offset):
                    status_insn = next_insn
                elif sp_insn is None and self._is_mov_to_r13_offset(next_insn, stack_ptr_offset):
                    sp_insn = next_insn
            break

        if ret_addr_insn is None:
            return False

        # 必须有 status_code 写入
        if status_insn is None:
            return False

        # 检查 status_code 是否属于可恢复集合
        status_immediate = self._get_immediate_from_mov(status_insn)
        if status_immediate is not None:
            if status_immediate not in self.aot_profile.resumable_statuses:
                return False

        # 检查指令顺序：return_address 必须在 status_code 之前
        # （而且它们都应该在 ret 之前）
        insns_list = list(insns)
        try:
            ret_addr_pos = insns_list.index(ret_addr_insn)
            status_pos = insns_list.index(status_insn)
            if ret_addr_pos >= status_pos:
                return False
        except ValueError:
            return False

        return True

    def _is_mov_to_r13_offset(self, insn: X86Instruction, expected_offset: int) -> bool:
        """检查指令是否为 MOV 到 [R13 + expected_offset]。"""
        if not insn.mnemonic.lower().startswith("mov"):
            return False
        operands = parse_operands(insn)
        if not operands.get("is_memory"):
            return False
        base_reg = operands.get("base_reg")
        if base_reg != Register.R13:
            return False
        offset = operands.get("offset")
        return offset == expected_offset

    def _get_immediate_from_mov(self, insn: X86Instruction) -> Optional[int]:
        """从 MOV 指令中提取立即数操作数，如果不是立即数则返回 None。"""
        operands = parse_operands(insn)
        return operands.get("immediate")

    def _get_or_create_go_host_node_for_ret(self, ret_block_addr: int) -> int:
        """为每个 ret 站点分配独立 GO_HOST 外部节点。"""
        go_addr = self._go_host_addr_by_ret_block.get(ret_block_addr)
        if go_addr is None:
            go_index = len(self._go_host_addr_by_ret_block)
            go_addr = self.GO_HOST_NODE_BASE_ADDR + go_index
            self._go_host_addr_by_ret_block[ret_block_addr] = go_addr
            self.cfg.get_or_create_external_node(go_addr, f"GO_HOST_{go_index}")
        else:
            self.cfg.get_or_create_external_node(go_addr, f"GO_HOST_{go_addr - self.GO_HOST_NODE_BASE_ADDR}")
        return go_addr

    def _load_exit_return_address(self, mstate: SMTState):
        """读取 callEngine.exitContext.returnAddress（64-bit）。"""
        r13_value = mstate.x86_registers.get_register(Register.R13)
        ret_addr_offset = BitVecVal(self.aot_profile.offsets["return_address"], 64)
        return mstate.x86_memory.load_64bit(r13_value + ret_addr_offset)

    def _handle_ret_with_go_bridge(self, global_state: X86GlobalState, mstate: SMTState,
                                   block: X86Block, insn: X86Instruction) -> List[X86GlobalState]:
        """处理 ret：支持 ret -> GO_HOST -> returnAddress 的动态建模。"""
        import copy as copy_module
        from utils.z3_helpers import analyze_jump_target

        # 默认行为：ret 终止（仅在识别到 CallGoFunction 模式时建模 GO 往返）
        if not self._is_call_go_function_pattern(block):
            setattr(global_state, "_ret_terminal_branch", True)
            return []

        # 每个 CallGoFunction 站点拥有自己的 GO_HOST 节点
        go_host_addr = self._get_or_create_go_host_node_for_ret(block.start_addr)
        self.cfg.add_edge(
            block.start_addr,
            go_host_addr,
            X86EdgeType.CALL,
            source_instruction=insn,
        )

        # 以当前状态为模板构建恢复分支
        resumed_states: List[X86GlobalState] = []
        return_addr_expr = self._load_exit_return_address(mstate)
        return_addr_analysis = analyze_jump_target(simplify(return_addr_expr))

        # GO 返回地址必须是静态常量（RIP 相对寻址）
        if not return_addr_analysis.is_static:
            from utils.exceptions import LogicError
            raise LogicError(
                "dynamic_return_address",
                f"GO return address at 0x{block.start_addr:x} must be static constant",
                "GO compileCallGoFunction always uses static return addresses"
            )

        for target_addr, _ in return_addr_analysis.targets:
            target_block = self.blocks_by_addr.get(target_addr)
            if target_block is None:
                continue

            resume_world_state = copy_module.copy(global_state.world_state)
            target_node = self.cfg.get_or_create_node(target_addr)

            resumed_state = X86GlobalState(
                mstate=mstate.copy(),
                world_state=resume_world_state,
                node=target_node,
            )
            # GO 往返不增加 depth，因为它是线性的而非分支
            resumed_state.depth = global_state.depth
            resumed_states.append(resumed_state)

            self.cfg.add_edge(
                go_host_addr,
                target_addr,
                X86EdgeType.RETURN,
            )

        # 仅动态结果决定是否终止：有恢复后继则非终止，否则终止。
        setattr(global_state, "_ret_terminal_branch", len(resumed_states) == 0)

        return resumed_states

    def _build_jump_condition(self, mnemonic: str, mstate: SMTState):
        """为条件跳转构建符号条件。

        Args:
            mnemonic: 指令助记符（jb、jae等）
            mstate: 机器状态

        Returns:
            符号条件（BoolRef）

        Note:
            从 CPU 标志寄存器（CF, ZF, SF, OF）中提取实际条件。
            标志位是 1 位 BitVec，使用 == 运算符比较得到 BoolRef。
        """
        # 获取 CPU 标志位（1 位 BitVec）
        cf = mstate.x86_registers.get_flag('CF')
        zf = mstate.x86_registers.get_flag('ZF')
        sf = mstate.x86_registers.get_flag('SF')
        of = mstate.x86_registers.get_flag('OF')

        # 将 1 位 BitVec 转换为 BoolRef
        # (flag == BitVecVal(1, 1)) 返回 BoolRef
        cf_true = (cf == BitVecVal(1, 1))
        cf_false = (cf == BitVecVal(0, 1))
        zf_true = (zf == BitVecVal(1, 1))
        zf_false = (zf == BitVecVal(0, 1))
        sf_eq_of = (sf == of)
        sf_ne_of = Not(sf == of)

        # 根据助记符构建条件
        # jl/jle/jg/jge 涉及 SF 和 OF 的关系
        conditions = {
            'jb': cf_true,           # CF == 1 (无符号小于)
            'jae': cf_false,         # CF == 0 (无符号大于等于)
            'ja': And(cf_false, zf_false),   # CF == 0 and ZF == 0 (无符号大于)
            'jbe': Or(cf_true, zf_true),     # CF == 1 or ZF == 1 (无符号小于等于)
            'je': zf_true,           # ZF == 1 (等于)
            'jne': zf_false,         # ZF == 0 (不等于)
            'jl': sf_ne_of,          # SF != OF (有符号小于)
            'jle': Or(zf_true, sf_ne_of),  # ZF == 1 or SF != OF (有符号小于等于)
            'jg': And(zf_false, sf_eq_of),  # ZF == 0 and SF == OF (有符号大于)
            'jge': sf_eq_of,         # SF == OF (有符号大于等于)
        }

        return conditions.get(mnemonic, zf_true)

    def _extract_jcc_condition(self, state: X86GlobalState):
        """从状态中提取 Jcc 条件（用于 CFG 边）。

        Args:
            state: 全局状态

        Returns:
            条件 BoolRef 或 None
        """
        from z3 import BoolVal, eq, And
        
        constraints = state.get_constraints()
        
        # 过滤掉初始的 True 约束，只获取实际添加的约束
        real_constraints = [
            c for c in constraints 
            if not (isinstance(c, type(BoolVal(True))) and eq(c, BoolVal(True)))
        ]
        
        if real_constraints:
            # 返回最后一个添加的约束（即跳转条件）
            return real_constraints[-1]
        
        # 如果没有实际约束，检查 flag_constraints
        if hasattr(constraints, 'flag_constraints'):
            flag_constraints = constraints.flag_constraints
            if flag_constraints:
                # 返回合并的标志约束
                return And(*flag_constraints.values())
        
        # 如果没有任何约束，返回最后一个约束（可能是初始的 True）
        if len(constraints) > 0:
            return list(constraints)[-1]
        
        return None

    def _handle_fallthrough(self, global_state: X86GlobalState, mstate: SMTState,
                           block: X86Block) -> List[X86GlobalState]:
        """处理顺序执行（fallthrough）。

        Args:
            global_state: 当前全局状态
            mstate: 执行后的机器状态
            block: 当前块

        Returns:
            新全局状态列表
        """
        import copy as copy_module

        # 找到下一个块
        current_idx = self.block_index[block.start_addr]
        if current_idx + 1 >= len(self.blocks):
            # 没有下一个块，返回空列表
            return []

        next_addr = self.blocks[current_idx + 1].start_addr
        next_node = self.cfg.get_or_create_node(next_addr)

        new_state = X86GlobalState(
            mstate=mstate,
            world_state=copy_module.copy(global_state.world_state),
            node=next_node
        )
        # fallthrough 不增加 depth，因为它是顺序执行而非分支
        new_state.depth = global_state.depth

        return [new_state]

    def _is_terminal_state(self, global_state: X86GlobalState) -> bool:
        """检查是否是终止状态。

        Args:
            global_state: 全局状态

        Returns:
            如果是终止状态则返回 True
        """
        node = global_state.node
        if node is None or not node.block.instructions:
            return False

        last_insn = node.block.instructions[-1]
        mnemonic = last_insn.mnemonic.lower()
        if mnemonic == 'ret':
            if not self.enable_go_bridge:
                return True

            # execute_state 已经为 ret 分流写入了标记，优先使用。
            marked_terminal = getattr(global_state, "_ret_terminal_branch", None)
            if marked_terminal is not None:
                return bool(marked_terminal) and global_state.get_constraints().is_possible()

            # 兜底：若未经过 execute_state，ret 默认按终止处理。
            return True

        # 非显式跳转/返回指令：若当前块已是最后一个块，则自然终止
        if mnemonic not in ['jmp', 'jb', 'jae', 'ja', 'jbe', 'je', 'jne', 'jl', 'jle', 'jg', 'jge']:
            idx = self.block_index.get(node.block.start_addr)
            return idx is not None and idx == len(self.blocks) - 1

        return False

    def _detect_and_handle_loops(self, global_state: X86GlobalState) -> None:
        """检测当前状态是否形成循环，并根据类型分类处理。

        TODO: 实现循环检测逻辑
        - 地址重复检测
        - 循环分类（静态/动态/无界）
        - 静态有界循环展开
        - 其他循环类型抛出 UnsupportedLoopError

        Args:
            global_state: 当前全局状态

        Raises:
            UnsupportedLoopError: 检测到不支持的循环类型时抛出
        """
        # TODO: 实现循环检测
        pass

    def _classify_loop(self, loop_addr: int, path_context: Dict) -> str:
        """判断循环类型。

        TODO: 实现循环分类逻辑
        - 静态有界：检查循环条件是否为常量比较
        - 动态有界：条件与符号变量比较
        - 无界：无法确定循环边界

        Args:
            loop_addr: 循环头的地址
            path_context: 执行路径上下文信息

        Returns:
            "static_bounded" | "dynamic_bounded" | "unbounded"
        """
        # TODO: 实现循环分类
        return "dynamic_bounded"  # 默认返回


def build_x86_dynamic_cfg(blocks: List[X86Block],
                          initial_state: SMTState,
                          strategy_cls: type = X86DFSStrategy,
                          max_depth: int = 100,
                          use_reachability_check: bool = True,
                          enable_go_bridge: bool = True,
                          enable_merge: bool = False) -> Tuple[List[X86GlobalState], X86DynamicCFG]:
    """构建动态 CFG 并执行符号执行。

    Args:
        blocks: x86-64 块列表
        initial_state: 初始机器状态
        strategy_cls: 搜索策略类
        max_depth: 最大执行深度
        use_reachability_check: 是否启用可达性检查
        enable_go_bridge: 是否启用 ret->GO_HOST->returnAddress 建模
        enable_merge: 是否启用合流点合并优化

    Returns:
        (final_states, cfg) 元组
    """
    executor = X86SymbolicExecutor(
        blocks,
        strategy_cls=strategy_cls,
        max_depth=max_depth,
        use_reachability_check=use_reachability_check,
        enable_go_bridge=enable_go_bridge,
        enable_merge=enable_merge,
    )
    final_states = executor.execute(initial_state)
    return final_states, executor.cfg
