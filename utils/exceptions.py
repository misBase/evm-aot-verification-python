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

