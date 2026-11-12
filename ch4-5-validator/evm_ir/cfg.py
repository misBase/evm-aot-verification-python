"""
EVM IR控制流图（CFG）构建和符号执行。

本模块完全参考 mythril 的设计实现：
- 节点+边的 CFG 结构
- 边执行边构建 CFG
- work_list 驱动的路径探索
- 状态注释系统
- 策略模式的搜索算法

代码已重构为模块化结构，此文件作为统一导出入口。
"""

# 从子模块导入所有公共 API
from .cfg_structures import EdgeType, CFGEdge, CFGNode, DynamicCFG
from .cfg_state import WorldState, Constraints, GlobalState
from .cfg_annotations import StateAnnotation, LoopCountAnnotation
from .cfg_strategies import (
    SearchStrategy, DFSStrategy, BFSStrategy,
    ExtensionStrategy, BoundedLoopsStrategy
)
from .cfg_executor import SymbolicExecutor, build_dynamic_cfg

__all__ = [
    # CFG 结构
    'EdgeType', 'CFGEdge', 'CFGNode', 'DynamicCFG',
    # 状态管理
    'WorldState', 'Constraints', 'GlobalState',
    # 状态注解
    'StateAnnotation', 'LoopCountAnnotation',
    # 搜索策略
    'SearchStrategy', 'DFSStrategy', 'BFSStrategy',
    'ExtensionStrategy', 'BoundedLoopsStrategy',
    # 符号执行引擎
    'SymbolicExecutor', 'build_dynamic_cfg',
]
