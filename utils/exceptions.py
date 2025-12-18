"""
Custom exceptions for verification tool.

This module defines custom exception classes for better error handling.
"""


class VerificationError(Exception):
    """Base exception for verification-related errors."""
    pass


class ParseError(VerificationError):
    """Exception raised when parsing fails.
    
    This can occur when:
    - JSON parsing fails
    - x86 hex string parsing fails
    - Invalid IR structure
    """
    pass


class VerificationTimeout(VerificationError):
    """Exception raised when verification times out.
    
    This occurs when the Z3 solver exceeds the configured timeout.
    """
    pass


class UnsupportedLoopError(VerificationError):
    """Exception raised when encountering unsupported loop types.
    
    This occurs when:
    - Unbounded loops are detected
    - Dynamically bounded loops are detected (not yet supported)
    """
    def __init__(self, loop_type: str, loop_info: str, message: str = ""):
        """Initialize UnsupportedLoopError.
        
        Args:
            loop_type: Type of loop ("unbounded" or "dynamically_bounded")
            loop_info: Information about the loop (e.g., block PCs)
            message: Additional error message
        """
        self.loop_type = loop_type
        self.loop_info = loop_info
        error_msg = f"Unsupported {loop_type} loop detected: {loop_info}"
        if message:
            error_msg += f". {message}"
        super().__init__(error_msg)

