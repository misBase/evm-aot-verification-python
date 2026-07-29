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


class LogicError(VerificationError):
    """逻辑错误时引发的异常。

    这可能发生在：
    - IR结构不一致（例如，静态跳转但目标块不存在）
    - 控制流图构建时的逻辑错误
    - 程序逻辑上的不一致
    """
    def __init__(self, error_code: str, error_info: str, message: str = ""):
        """初始化LogicError。

        Args:
            error_code: 错误代码（例如，"dynamic_return_address"）
            error_info: 关于错误的信息（例如，块地址）
            message: 附加错误消息
        """
        self.error_code = error_code
        self.error_info = error_info
        error_msg = f"Logic error ({error_code}): {error_info}"
        if message:
            error_msg += f". {message}"
        super().__init__(error_msg)


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


class UnsupportedCallEngineAccessError(VerificationError):
    """机器码对 callEngine 已知字段的访问形态超出建模假设时引发。

    与 LogicError 的区别：不是 IR/CFG 结构不一致，而是 x86 指令形态（写入宽度）
    与 side-channel 建模假设不符。静默跳过会让后续读取拿到陈旧值，方向朝假绿。
    """
    def __init__(self, offset: int, size_bytes, expected_sizes, message: str = ""):
        """初始化UnsupportedCallEngineAccessError。

        Args:
            offset: callEngine 字段偏移（例如 0xE0）
            size_bytes: 实际访问宽度（字节）
            expected_sizes: 该偏移已建模的宽度集合
            message: 附加错误消息
        """
        self.offset = offset
        self.size_bytes = size_bytes
        self.expected_sizes = expected_sizes
        expected = ", ".join(str(s) for s in sorted(expected_sizes))
        error_msg = (
            f"Unsupported callEngine access at [r13+{offset:#x}]: "
            f"size={size_bytes} bytes, modeled size(s)={{{expected}}}"
        )
        if message:
            error_msg += f". {message}"
        super().__init__(error_msg)


class UnsupportedJumpError(VerificationError):
    """遇到不支持的跳转类型时引发的异常。

    这发生在：
    - 检测到动态跳转（JUMP或JUMPI）
    - 跳转目标无法在编译时确定
    """
    def __init__(self, jump_type: str, jump_info: str, message: str = ""):
        """初始化UnsupportedJumpError。

        Args:
            jump_type: 跳转类型（"dynamic_jump"或"dynamic_jumpi"）
            jump_info: 关于跳转的信息（例如，块PC）
            message: 附加错误消息
        """
        self.jump_type = jump_type
        self.jump_info = jump_info
        error_msg = f"Unsupported {jump_type} detected: {jump_info}"
        if message:
            error_msg += f". {message}"
        super().__init__(error_msg)

