"""
验证工具的自定义异常。

本模块定义自定义异常类以更好地处理错误。
"""


class VerificationError(Exception):
    """验证相关错误的基础异常。"""
    pass


class ParseError(VerificationError):
    """解析失败时引发的异常。
    
    这可能发生在：
    - JSON解析失败
    - x86十六进制字符串解析失败
    - 无效的IR结构
    """
    pass


class VerificationTimeout(VerificationError):
    """验证超时时引发的异常。
    
    当Z3求解器超过配置的超时时间时发生。
    """
    pass


class UnsupportedLoopError(VerificationError):
    """遇到不支持的循环类型时引发的异常。
    
    这发生在：
    - 检测到无界循环
    - 检测到动态有界循环（尚不支持）
    """
    def __init__(self, loop_type: str, loop_info: str, message: str = ""):
        """初始化UnsupportedLoopError。
        
        Args:
            loop_type: 循环类型（"unbounded"或"dynamically_bounded"）
            loop_info: 关于循环的信息（例如，块PC）
            message: 附加错误消息
        """
        self.loop_type = loop_type
        self.loop_info = loop_info
        error_msg = f"Unsupported {loop_type} loop detected: {loop_info}"
        if message:
            error_msg += f". {message}"
        super().__init__(error_msg)

