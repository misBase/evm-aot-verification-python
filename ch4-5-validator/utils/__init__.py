"""
验证工具的实用模块。

本包包含实用类和辅助函数。
"""

from .config import VerificationConfig
from .exceptions import (
    VerificationError,
    ParseError,
    VerificationTimeout,
)

__all__ = [
    'VerificationConfig',
    'VerificationError',
    'ParseError',
    'VerificationTimeout',
]

