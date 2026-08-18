"""
Status Code 定义模块。

定义与 Go 项目 go-hpc-evm 中 evmNativeCallStatusCode 对应的枚举，
用于 IR 层面和机器码层面的执行结果验证。
"""

from enum import IntEnum
from typing import Dict, TYPE_CHECKING

from z3 import BitVecVal

if TYPE_CHECKING:
    from state.smt_state import SMTState


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


def get_status_message(code: EvmStatusCode) -> str:
    """获取状态码对应的错误消息。"""
    return STATUS_CODE_MESSAGES.get(code, "Unknown status code")


def set_terminal_status(state: "SMTState", code: EvmStatusCode) -> None:
    """把终止状态码写进 state，``error_string`` 由状态码单向投影得出。

    这是两者的**唯一**写入点。各写各的会漂（历史上 STOP 曾写成 RETURNED 的
    字面量），做成投影关系后结构上不可能再漂。

    ``error_code`` 是权威值（参与 等价性比较），``error_string`` 只用于诊断。
    """
    state.error_code = BitVecVal(int(code), 8)
    state.error_string = get_status_message(code)
