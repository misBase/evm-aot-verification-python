"""x86-64指令语义建模。

使用基于 evm_ir 设计的动态 CFG 构建和 worklist 驱动的符号执行。
"""

# 核心模型和语义
from .semantics import X86SemanticsModel
from .models import X86Block, X86Instruction, Register
from .aot_profile import AOT_COMPILER_PROFILE, X86AOTProfile

# 新的 CFG 和符号执行架构 (参考 evm_ir)
from .cfg_structures import X86EdgeType, X86CFGEdge, X86CFGNode, X86DynamicCFG
from .cfg_state import X86Constraints, X86WorldState, X86GlobalState
from .cfg_annotations import X86StateAnnotation, LoopDetectionAnnotation
from .cfg_strategies import (
    X86SearchStrategy,
    X86DFSStrategy,
    X86BFSStrategy,
    X86ExtensionStrategy,
    X86BoundedLoopsStrategy
)
from .cfg_executor import X86SymbolicExecutor, build_x86_dynamic_cfg

from .disassembler import disassemble_hex, parse_operands
from .program import X86Program
from .cfg import identify_basic_blocks

__all__ = [
    # 核心模型和语义
    'X86SemanticsModel',
    'X86Block',
    'X86Instruction',
    'Register',
    'X86AOTProfile',
    'AOT_COMPILER_PROFILE',

    # 新的 CFG 和符号执行架构
    'X86EdgeType',
    'X86CFGEdge',
    'X86CFGNode',
    'X86DynamicCFG',
    'X86Constraints',
    'X86WorldState',
    'X86GlobalState',
    'X86StateAnnotation',
    'LoopDetectionAnnotation',
    'X86SearchStrategy',
    'X86DFSStrategy',
    'X86BFSStrategy',
    'X86ExtensionStrategy',
    'X86BoundedLoopsStrategy',
    'X86SymbolicExecutor',
    'build_x86_dynamic_cfg',

    'disassemble_hex',
    'parse_operands',
    'X86Program',
    'identify_basic_blocks',
]
