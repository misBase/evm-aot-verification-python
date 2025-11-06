"""EVM IR processing and semantic modeling."""

from .json_parser import load_ir_from_json
from .models import EVMBlock, EvmOperator
from .semantics import EVMIRSemantics, EVMOperationSemantics

__all__ = [
    'load_ir_from_json',
    'EVMBlock',
    'EvmOperator',
    'EVMIRSemantics',
    'EVMOperationSemantics',
]

