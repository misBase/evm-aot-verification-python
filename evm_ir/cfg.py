"""
EVM IR控制流图（CFG）构建和路径分析。

本模块为EVM IR程序提供CFG构建和路径查找。
级别2：CFG级路径合并。
"""

from typing import List, Dict, Set, Tuple, Optional
from .models import EVMBlock, EvmOperator
from z3 import BoolRef, BoolVal, And, Or, Not


class IRCFG:
    """EVM IR块的控制流图。"""
    
    def __init__(self, blocks: List[EVMBlock]):
        """从块初始化CFG。
        
        Args:
            blocks: EVM块列表
        """
        self.blocks = blocks
        self.blocks_by_pc: Dict[int, EVMBlock] = {block.pc: block for block in blocks}
        
        # 构建CFG：块 -> 后继块列表
        self.successors: Dict[int, List[EVMBlock]] = {}
        self._build_cfg()
    
    def _build_cfg(self):
        """从块构建控制流图。"""
        # 初始化所有块的后继
        for block in self.blocks:
            self.successors[block.pc] = []
        
        # 基于JUMP/JUMPI操作查找后继
        for i, block in enumerate(self.blocks):
            # 检查块中的最后一个操作
            if not block.operations:
                continue
            
            last_op = block.operations[-1]
            kind = last_op.kind.upper()
            
            if kind == "JUMP":
                # 无条件跳转：查找目标块
                # 如果JUMP有immediate值（静态跳转），使用它作为目标PC
                if last_op.immediate is not None and last_op.is_static:
                    target_pc = last_op.immediate
                    target_block = self.blocks_by_pc.get(target_pc)
                    if target_block:
                        self.successors[block.pc].append(target_block)
                    else:
                        # 静态跳转但找不到目标块：这是逻辑错误
                        from utils.exceptions import LogicError
                        error_msg = f"Static JUMP at pc={last_op.pc} in block pc={block.pc} targets pc={target_pc}, but target block not found in CFG"
                        raise LogicError(error_msg)
                else:
                    # 动态跳转：不支持
                    from utils.exceptions import UnsupportedJumpError
                    jump_info = f"Dynamic JUMP at pc={last_op.pc} in block pc={block.pc}"
                    raise UnsupportedJumpError("dynamic_jump", jump_info, "Dynamic jumps are not supported by this framework")

            elif kind == "JUMPI":
                # 条件跳转：两个后继（跳转和顺序执行）
                # 跳转目标：如果JUMPI有immediate值（静态跳转），使用它作为目标PC
                if last_op.immediate is not None and last_op.is_static:
                    target_pc = last_op.immediate
                    target_block = self.blocks_by_pc.get(target_pc)
                    if target_block:
                        self.successors[block.pc].append(target_block)
                    else:
                        # 静态跳转但找不到目标块：这是逻辑错误
                        from utils.exceptions import LogicError
                        error_msg = f"Static JUMPI at pc={last_op.pc} in block pc={block.pc} targets pc={target_pc}, but target block not found in CFG"
                        raise LogicError(error_msg)
                else:
                    # 动态条件跳转：不支持
                    from utils.exceptions import UnsupportedJumpError
                    jump_info = f"Dynamic JUMPI at pc={last_op.pc} in block pc={block.pc}"
                    raise UnsupportedJumpError("dynamic_jumpi", jump_info, "Dynamic conditional jumps are not supported by this framework")

                # 顺序执行：下一个块（条件为False时）
                if i + 1 < len(self.blocks):
                    self.successors[block.pc].append(self.blocks[i + 1])
            
            elif kind in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]:
                # 终止块：无后继
                pass
            
            else:
                # 普通块：顺序执行到下一个块
                if i + 1 < len(self.blocks):
                    self.successors[block.pc].append(self.blocks[i + 1])
    
    def get_entry_block(self) -> EVMBlock:
        """获取入口块（第一个块）。
        
        Returns:
            入口块
        """
        if not self.blocks:
            raise ValueError("No blocks in CFG")
        return self.blocks[0]
    
    def get_terminal_blocks(self) -> List[EVMBlock]:
        """获取所有终止块（以STOP/RETURN/REVERT结尾的块）。
        
        Returns:
            终止块列表
        """
        terminals = []
        for block in self.blocks:
            if not block.operations:
                continue
            last_op = block.operations[-1]
            if last_op.kind.upper() in ["STOP", "RETURN", "REVERT", "SELFDESTRUCT"]:
                terminals.append(block)
        return terminals
    
    def find_all_paths(self, entry: Optional[EVMBlock] = None, 
                      terminals: Optional[List[EVMBlock]] = None) -> List[Tuple[List[EVMBlock], BoolRef]]:
        """查找从入口到终止块的所有路径。
        
        Args:
            entry: 入口块（默认：第一个块）
            terminals: 终止块（默认：所有终止块）
            
        Returns:
            (path, condition)元组列表，其中：
            - path: 按执行顺序排列的块列表
            - condition: 此路径的符号条件（来自JUMPI操作）
        """
        if entry is None:
            entry = self.get_entry_block()
        if terminals is None:
            terminals = self.get_terminal_blocks()
        
        if not terminals:
            # 如果没有明确的终止块，使用最后一个块
            terminals = [self.blocks[-1]] if self.blocks else []
        
        all_paths = []
        visited = set()
        
        def dfs(current: EVMBlock, path: List[EVMBlock], condition: BoolRef):
            """深度优先搜索以查找所有路径。"""
            # 避免循环（简单检查）
            if current in path:
                return
            
            current_path = path + [current]
            
            # 检查是否到达终止块
            if current in terminals:
                all_paths.append((current_path, condition))
                return
            
            # 探索后继
            for successor in self.successors.get(current.pc, []):
                # 目前，条件始终为True（我们稍后将使用JUMPI条件增强此功能）
                dfs(successor, current_path, condition)
        
        # 从入口开始DFS
        dfs(entry, [], BoolVal(True))
        
        return all_paths
    
    def get_successors(self, block: EVMBlock) -> List[EVMBlock]:
        """获取给定块的后继块。
        
        Args:
            block: 要获取后继的块
            
        Returns:
            后继块列表
        """
        return self.successors.get(block.pc, [])
    
    def detect_loops(self) -> List[Tuple[List[EVMBlock], str]]:
        """检测CFG中的所有循环并分类。
        
        Returns:
            (loop_blocks, loop_type)元组列表，其中：
            - loop_blocks: 循环中的块列表
            - loop_type: "static_bounded"、"dynamically_bounded"或"unbounded"
        """
        # 查找强连通分量（SCC），它们表示循环
        sccs = self._find_strongly_connected_components()
        
        loops = []
        for scc in sccs:
            # 循环是包含多个块的SCC，或者是自循环
            if len(scc) > 1 or self._is_self_loop(scc[0]):
                loop_type = self._classify_loop(scc)
                loops.append((scc, loop_type))
        
        return loops
    
    def validate_loops(self):
        """验证循环，对不支持的循环类型抛出异常。
        
        这应在符号执行之前调用，以检测并拒绝不支持的循环
        （无界和动态有界）。
        
        Raises:
            UnsupportedLoopError: 如果检测到无界或动态有界循环
        """
        from utils.exceptions import UnsupportedLoopError
        
        loops = self.detect_loops()
        
        for loop_blocks, loop_type in loops:
            if loop_type == "unbounded":
                loop_info = f"Unbounded loop detected in blocks: {[b.pc for b in loop_blocks]}"
                raise UnsupportedLoopError(
                    "unbounded",
                    loop_info,
                    "Unbounded loops are not supported. Please use bounded loops or static loop unrolling."
                )
            elif loop_type == "dynamically_bounded":
                loop_info = f"Dynamically bounded loop detected in blocks: {[b.pc for b in loop_blocks]}"
                raise UnsupportedLoopError(
                    "dynamically_bounded",
                    loop_info,
                    "Dynamically bounded loops are not yet supported. Only statically bounded loops are supported."
                )
            # 静态有界循环受支持，无需错误
    
    def _find_strongly_connected_components(self) -> List[List[EVMBlock]]:
        """使用Tarjan算法查找所有强连通分量（SCC）。
        
        SCC表示循环：如果一组块形成SCC，它们可以相互到达。
        
        Returns:
            SCC列表，其中每个SCC是一个块列表
        """
        # TODO: 实现用于查找SCC的Tarjan算法
        # 目前，返回空列表（未检测到循环）
        # 算法概述：
        # 1. 使用深度优先搜索，跟踪索引和lowlink
        # 2. 当节点的lowlink等于其索引时，它是SCC的根
        # 3. 从栈中弹出所有节点直到根，形成SCC
        
        return []
    
    def _is_self_loop(self, block: EVMBlock) -> bool:
        """检查块是否是自循环（跳转到自身）。
        
        Args:
            block: 要检查的块
            
        Returns:
            如果块跳转到自身则返回True，否则返回False
        """
        # 检查块是否在自己的后继中
        return block in self.successors.get(block.pc, [])
    
    def _classify_loop(self, loop_blocks: List[EVMBlock]) -> str:
        """分类循环类型：静态有界、动态有界或无界。
        
        分类策略：
        1. 检查循环退出条件是否为常量或编译时可确定
        2. 检查循环是否有显式迭代变量和界限
        
        Args:
            loop_blocks: 循环中的块列表
            
        Returns:
            "static_bounded"、"dynamically_bounded"或"unbounded"
        """
        # TODO: 实现循环分类算法
        # 目前，保守地返回"unbounded"作为默认值
        # 算法概述：
        # 1. 分析循环块中的退出条件（JUMPI指令）
        # 2. 检查退出条件是否为常量（静态有界）
        # 3. 检查退出条件是否有符号但有界的变量（动态有界）
        # 4. 否则，分类为无界
        
        # 检查退出条件
        exit_conditions = []
        for block in loop_blocks:
            if not block.operations:
                continue
            last_op = block.operations[-1]
            if last_op.kind.upper() == "JUMPI":
                exit_conditions.append(block)
        
        if not exit_conditions:
            # 未找到退出条件，可能是无界
            return "unbounded"
        
        # 检查循环是否有迭代计数器
        has_counter = self._has_iteration_counter(loop_blocks)
        
        if has_counter:
            # 有迭代计数器，但需要检查界限是否为常量
            # 目前，保守地分类为动态有界
            return "dynamically_bounded"
        
        # 没有清晰的迭代模式，分类为无界
        return "unbounded"
    
    def _has_iteration_counter(self, loop_blocks: List[EVMBlock]) -> bool:
        """检查循环是否有迭代计数器。
        
        这是一个简化的检查。更复杂的实现将：
        - 查找形成计数器模式的PUSH、ADD、SUB操作
        - 跟踪循环内的变量修改
        
        Args:
            loop_blocks: 循环中的块列表
            
        Returns:
            如果循环似乎有迭代计数器则返回True，否则返回False
        """
        # TODO: 实现迭代计数器检测
        # 目前，返回False（无法确定）
        # 算法概述：
        # 1. 查找递增/递减值的操作（带常量的ADD/SUB）
        # 2. 检查此值是否用于退出条件
        # 3. 模式：PUSH initial_value，循环：ADD/SUB常量，与界限比较
        
        return False


def build_ir_cfg(blocks: List[EVMBlock]) -> IRCFG:
    """从IR块构建CFG。
    
    Args:
        blocks: EVM块列表
        
    Returns:
        IRCFG实例
    """
    return IRCFG(blocks)

