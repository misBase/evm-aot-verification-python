"""EVM IR处理和语义建模。"""

from .json_parser import load_ir_from_json, CompilerEVMResult
from .models import EVMBlock, EvmOperator
from .semantics import EVMIRSemantics, EVMOperationSemantics
from .program import EVMProgram

__all__ = [
    'load_ir_from_json',
    'CompilerEVMResult',
    'EVMBlock',
    'EvmOperator',
    'EVMIRSemantics',
    'EVMOperationSemantics',
    'EVMProgram',
]

