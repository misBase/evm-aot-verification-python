#!/usr/bin/env python3
"""
EVM AOT翻译验证工具

此脚本验证EVM IR（来自JSON）和AOT编译的x86-64机器码（来自十六进制字符串）
之间的语义等价性。

用法：
    python main.py <ir_json_path> <x86_hex> [--base-addr ADDR] [--timeout MS] [--verbose]
"""

import argparse
import sys
from evm_ir.program import EVMProgram
from evm_ir.json_parser import load_ir_from_json
from x86_64.program import X86Program
from verification.program_verifier import ProgramEquivalenceChecker


def parse_args():
    """解析命令行参数。"""
    parser = argparse.ArgumentParser(
        description="验证EVM IR和x86-64机器码之间的语义等价性",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例：
  python main.py tests/data/example_ir.json 498b46c0490346e0...
  python main.py contract.ir.json 498b46c0... --base-addr 0x6c
  python main.py contract.ir.json 498b46c0... --timeout 30000 --verbose
        """
    )
    
    parser.add_argument(
        'ir_json_path',
        help='Path to EVM IR JSON file'
    )
    
    parser.add_argument(
        'x86_hex',
        help='x86-64 machine code as hex string'
    )
    
    parser.add_argument(
        '--base-addr',
        type=lambda x: int(x, 0),  # 接受十六进制或十进制
        default=0,
        metavar='ADDR',
        help='Base address for x86 code (default: 0)'
    )
    
    parser.add_argument(
        '--timeout', '-t',
        type=int,
        default=60000,
        metavar='MS',
        help='Z3 solver timeout in milliseconds (default: 60000)'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    
    return parser.parse_args()


def verify_programs(ir_json_path: str, x86_hex: str, base_addr: int, timeout_ms: int, verbose: bool):
    """验证EVM和x86程序之间的等价性。
    
    Args:
        ir_json_path: EVM IR JSON文件路径
        x86_hex: 十六进制编码的x86机器码
        base_addr: x86代码的基址
        timeout_ms: 求解器超时（毫秒）
        verbose: 启用详细输出
        
    Returns:
        (verified, message)，如果程序等价则verified为True
    """
    if verbose:
        print(f"Loading EVM IR from: {ir_json_path}")
        print(f"Loading x86 code from hex: {x86_hex[:64]}..." if len(x86_hex) > 64 else f"Loading x86 code from hex: {x86_hex}")
        print(f"Base address: 0x{base_addr:x}")
        print(f"Timeout: {timeout_ms}ms")
        print()
    
    # 从JSON加载EVM程序
    try:
        compiler_result = load_ir_from_json(ir_json_path)
        evm_program = EVMProgram(compiler_result)
    except FileNotFoundError:
        return False, f"Error: File not found: {ir_json_path}"
    except Exception as e:
        return False, f"Error loading EVM IR: {e}"
    
    # 从十六进制创建x86程序
    try:
        x86_program = X86Program.from_hex(x86_hex, base_addr=base_addr)
    except Exception as e:
        return False, f"Error parsing x86 hex: {e}"
    
    # 使用ProgramEquivalenceChecker验证
    checker = ProgramEquivalenceChecker(timeout_ms=timeout_ms, verbose=verbose)
    initial_state = ProgramEquivalenceChecker.create_default_initial_state()
    return checker.verify_program_pair(evm_program, x86_program, initial_state)


def main():
    """主入口点。"""
    args = parse_args()
    
    if args.verbose:
        print("=" * 70)
        print("EVM AOT TRANSLATION VERIFICATION")
        print("=" * 70)
        print()
    
    # 验证程序
    verified, message = verify_programs(
        args.ir_json_path,
        args.x86_hex,
        args.base_addr,
        args.timeout,
        args.verbose
    )
    
    # 输出结果
    if verified:
        print("✓ VERIFIED: Programs are semantically equivalent")
        if args.verbose and message:
            print(f"  {message}")
        return 0
    else:
        print("✗ VERIFICATION FAILED")
        if message:
            print(f"  {message}")
        return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\n\nInterrupted by user", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"\n\nError: {e}", file=sys.stderr)
        if '--verbose' in sys.argv or '-v' in sys.argv:
            import traceback
            traceback.print_exc()
        sys.exit(1)
