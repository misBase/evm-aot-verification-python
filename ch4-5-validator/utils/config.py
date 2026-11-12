"""
验证的配置管理。

本模块为验证工具提供配置类。
"""

from dataclasses import dataclass
from typing import Optional


@dataclass
class VerificationConfig:
    """验证配置。
    
    Attributes:
        timeout_ms: 求解器超时（毫秒）（默认：60000）
        verbose: 启用详细输出（默认：False）
        base_addr: x86代码的基址（默认：0）
        solver_timeout: Z3求解器超时（毫秒）（默认：60000）
    """
    timeout_ms: int = 60000
    verbose: bool = False
    base_addr: int = 0
    solver_timeout: int = 60000
    
    @classmethod
    def from_args(cls, args) -> 'VerificationConfig':
        """从命令行参数创建配置。
        
        Args:
            args: 解析的命令行参数（来自argparse）
            
        Returns:
            VerificationConfig实例
        """
        return cls(
            timeout_ms=getattr(args, 'timeout', 60000),
            verbose=getattr(args, 'verbose', False),
            base_addr=getattr(args, 'base_addr', 0),
            solver_timeout=getattr(args, 'timeout', 60000),
        )

