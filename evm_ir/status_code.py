"""
Status Code 定义模块。

定义与 Go 项目 go-hpc-evm 中 evmNativeCallStatusCode 对应的枚举，
用于 IR 层面和机器码层面的执行结果验证。
"""

from enum import IntEnum
from typing import Dict, Optional


class EvmStatusCode(IntEnum):
    """
    EVM 执行状态码 - 与 Go 项目 engine_evm.go 中的定义对应
    
    对应关系：
    - Go: evmNativeCallStatusCodeReturned = iota (0)
    - Python: RETURNED = 0
    """
    # 正常执行结果 (0-11)
    RETURNED = 0                      # 正常返回
    REVERTED = 1                      # 执行回滚
    STOPPED = 2                       # 停止执行
    INVALID = 3                       # 无效操作码
    CALL_GO_HOST_FUNCTION = 4         # 调用 Go 主机函数
    CALL_BUILT_IN_FUNCTION = 5         # 调用内置函数
    WRITE_PROTECTION = 6               # 写保护错误
    RETURN_DATA_OUT_OF_BOUNDS = 7      # 返回数据越界
    INVALID_JUMP = 8                   # 无效跳转
    INVALID_RETSUB = 9                # 无效返回子程序
    RETURN_STACK_EXCEEDED = 10         # 返回栈超出
    INVALID_SUBROUTINE_ENTRY = 11      # 无效子程序入口
    
    # 错误状态 (12-16)
    OUT_OF_GAS = 12                   # Gas 不足
    GAS_UINT_OVERFLOW = 13             # Gas 计算溢出
    STACK_UNDERFLOW = 14               # 栈下溢
    STACK_REACHED_LIMIT = 15           # 栈达到限制
    MAX_INIT_CODE_SIZE_EXCEEDED = 16  # 初始化代码过大
    
    # 调试状态
    DEBUG = 17                         # 调试模式


# Status Code 到错误消息的映射
STATUS_CODE_MESSAGES: Dict[EvmStatusCode, str] = {
    EvmStatusCode.RETURNED: "stop token",
    EvmStatusCode.REVERTED: "Execution reverted",
    EvmStatusCode.STOPPED: "execution stopped",
    EvmStatusCode.INVALID: "Invalid opcode",
    EvmStatusCode.CALL_GO_HOST_FUNCTION: "Calling Go host function",
    EvmStatusCode.CALL_BUILT_IN_FUNCTION: "Calling built-in function",
    EvmStatusCode.WRITE_PROTECTION: "Write protection violation",
    EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS: "Return data out of bounds",
    EvmStatusCode.INVALID_JUMP: "Invalid jump destination",
    EvmStatusCode.INVALID_RETSUB: "Invalid return from subroutine",
    EvmStatusCode.RETURN_STACK_EXCEEDED: "Return stack exceeded",
    EvmStatusCode.INVALID_SUBROUTINE_ENTRY: "Invalid subroutine entry",
    EvmStatusCode.OUT_OF_GAS: "Out of gas",
    EvmStatusCode.GAS_UINT_OVERFLOW: "Gas uint overflow",
    EvmStatusCode.STACK_UNDERFLOW: "Stack underflow",
    EvmStatusCode.STACK_REACHED_LIMIT: "Stack reached limit",
    EvmStatusCode.MAX_INIT_CODE_SIZE_EXCEEDED: "Max init code size exceeded",
    EvmStatusCode.DEBUG: "Debug mode",
}


ERROR_MESSAGE_TO_STATUS_CODE: Dict[str, EvmStatusCode] = {
    message: code for code, message in STATUS_CODE_MESSAGES.items()
}


def get_status_message(code: EvmStatusCode) -> str:
    """获取状态码对应的错误消息。"""
    return STATUS_CODE_MESSAGES.get(code, "Unknown status code")


def get_status_code_from_error(error_message: Optional[str]) -> Optional[EvmStatusCode]:
    """根据错误消息获取对应的状态码。"""
    if error_message is None:
        return None
    return ERROR_MESSAGE_TO_STATUS_CODE.get(error_message)


def is_error_status(code: EvmStatusCode) -> bool:
    """判断是否为错误状态码。"""
    return code in (
        EvmStatusCode.INVALID,
        EvmStatusCode.WRITE_PROTECTION,
        EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS,
        EvmStatusCode.INVALID_JUMP,
        EvmStatusCode.INVALID_RETSUB,
        EvmStatusCode.RETURN_STACK_EXCEEDED,
        EvmStatusCode.INVALID_SUBROUTINE_ENTRY,
        EvmStatusCode.OUT_OF_GAS,
        EvmStatusCode.GAS_UINT_OVERFLOW,
        EvmStatusCode.STACK_UNDERFLOW,
        EvmStatusCode.STACK_REACHED_LIMIT,
        EvmStatusCode.MAX_INIT_CODE_SIZE_EXCEEDED,
    )


def is_termination_status(code: EvmStatusCode) -> bool:
    """判断是否为终止执行的状态码。"""
    return code in (
        EvmStatusCode.RETURNED,
        EvmStatusCode.REVERTED,
        EvmStatusCode.STOPPED,
        EvmStatusCode.INVALID,
        EvmStatusCode.OUT_OF_GAS,
        EvmStatusCode.STACK_UNDERFLOW,
        EvmStatusCode.STACK_REACHED_LIMIT,
    )