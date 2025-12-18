"""
Configuration management for verification.

This module provides configuration classes for the verification tool.
"""

from dataclasses import dataclass
from typing import Optional


@dataclass
class VerificationConfig:
    """Verification configuration.
    
    Attributes:
        timeout_ms: Solver timeout in milliseconds (default: 60000)
        verbose: Enable verbose output (default: False)
        base_addr: Base address for x86 code (default: 0)
        solver_timeout: Z3 solver timeout in milliseconds (default: 60000)
    """
    timeout_ms: int = 60000
    verbose: bool = False
    base_addr: int = 0
    solver_timeout: int = 60000
    
    @classmethod
    def from_args(cls, args) -> 'VerificationConfig':
        """Create configuration from command-line arguments.
        
        Args:
            args: Parsed command-line arguments (from argparse)
            
        Returns:
            VerificationConfig instance
        """
        return cls(
            timeout_ms=getattr(args, 'timeout', 60000),
            verbose=getattr(args, 'verbose', False),
            base_addr=getattr(args, 'base_addr', 0),
            solver_timeout=getattr(args, 'timeout', 60000),
        )

