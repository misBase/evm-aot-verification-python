#!/usr/bin/env python3
"""
Unit tests for the EVM AOT verification system.
"""

import unittest
from z3 import simplify, BitVecVal
from evm_interpreter import EVMInterpreter, Uint256, EVMStack
from x86_semantics import X86Executor, Register
from verifier import TranslationVerifier


class TestUint256(unittest.TestCase):
    """Test the Uint256 class."""
    
    def test_from_int(self):
        """Test creating Uint256 from integer."""
        val = Uint256.from_int(0x70)
        bv = val.to_bv256()
        expected = BitVecVal(0x70, 256)
        self.assertTrue(simplify(bv == expected))
    
    def test_limb_layout(self):
        """Test that limbs are in correct order."""
        val = Uint256.from_int(0x123456789ABCDEF0)
        # Check that z0 contains the least significant bits
        self.assertEqual(simplify(val.z0), 0x123456789ABCDEF0)
        self.assertEqual(simplify(val.z1), 0)
        self.assertEqual(simplify(val.z2), 0)
        self.assertEqual(simplify(val.z3), 0)


class TestEVMStack(unittest.TestCase):
    """Test the EVM stack."""
    
    def test_push_pop(self):
        """Test basic push and pop operations."""
        stack = EVMStack()
        val = Uint256.from_int(42)
        stack.push(val)
        self.assertEqual(len(stack), 1)
        
        popped = stack.pop()
        self.assertEqual(len(stack), 0)
        # Check that the values match
        self.assertTrue(simplify(popped.to_bv256() == val.to_bv256()))
    
    def test_underflow(self):
        """Test that stack underflow raises an error."""
        stack = EVMStack()
        with self.assertRaises(IndexError):
            stack.pop()


class TestEVMInterpreter(unittest.TestCase):
    """Test the EVM interpreter."""
    
    def test_push1(self):
        """Test PUSH1 opcode."""
        interp = EVMInterpreter()
        interp.push1(0x60)
        self.assertEqual(len(interp.stack), 1)
        
        top = interp.get_top()
        expected = Uint256.from_int(0x60)
        self.assertTrue(simplify(top.to_bv256() == expected.to_bv256()))
    
    def test_add_simple(self):
        """Test ADD with simple values."""
        interp = EVMInterpreter()
        interp.push1(0x60)
        interp.push1(0x10)
        result = interp.add()
        
        expected = Uint256.from_int(0x70)
        self.assertTrue(simplify(result.to_bv256() == expected.to_bv256()))
    
    def test_add_overflow(self):
        """Test ADD with overflow."""
        interp = EVMInterpreter()
        interp.push1(0xFF)
        interp.push1(0xFF)
        result = interp.add()
        
        expected = Uint256.from_int(0x1FE)
        self.assertTrue(simplify(result.to_bv256() == expected.to_bv256()))
    
    def test_execute_bytecode(self):
        """Test executing complete bytecode."""
        interp = EVMInterpreter()
        bytecode = bytes([0x60, 0x60, 0x60, 0x10, 0x01])  # PUSH 0x60, PUSH 0x10, ADD
        result = interp.execute_bytecode(bytecode)
        
        expected = Uint256.from_int(0x70)
        self.assertTrue(simplify(result.to_bv256() == expected.to_bv256()))


class TestX86Executor(unittest.TestCase):
    """Test the x86-64 executor."""
    
    def test_mov_reg_imm(self):
        """Test MOV register, immediate."""
        executor = X86Executor()
        executor.mov_reg_imm(Register.RAX, 0x60)
        
        rax_val = executor.state.get_reg(Register.RAX)
        self.assertEqual(simplify(rax_val), 0x60)
    
    def test_add_reg_imm(self):
        """Test ADD register, immediate."""
        executor = X86Executor()
        executor.mov_reg_imm(Register.RAX, 0x60)
        executor.add_reg_imm(Register.RAX, 0x10)
        
        rax_val = executor.state.get_reg(Register.RAX)
        self.assertEqual(simplify(rax_val), 0x70)
    
    def test_adc_carry_propagation(self):
        """Test ADC carry propagation."""
        executor = X86Executor()
        
        # Set up: RAX = 0xFFFFFFFFFFFFFFFF, add 1
        executor.mov_reg_imm(Register.RAX, 0xFFFFFFFFFFFFFFFF)
        executor.add_reg_imm(Register.RAX, 1)
        
        # RAX should be 0, carry should be set
        rax_val = executor.state.get_reg(Register.RAX)
        self.assertEqual(simplify(rax_val), 0)
        
        # ADC with 0 should add the carry
        executor.mov_reg_imm(Register.RCX, 0)
        executor.adc_reg_imm(Register.RCX, 0)
        
        rcx_val = executor.state.get_reg(Register.RCX)
        self.assertEqual(simplify(rcx_val), 1)
    
    def test_execute_aot_add(self):
        """Test complete AOT ADD execution."""
        executor = X86Executor()
        result = executor.execute_aot_add(0x60, 0x10)
        
        expected = BitVecVal(0x70, 256)
        self.assertTrue(simplify(result == expected))


class TestVerifier(unittest.TestCase):
    """Test the verification engine."""
    
    def test_verify_concrete_add(self):
        """Test verification of concrete ADD operation."""
        verifier = TranslationVerifier(timeout_ms=10000, verbose=False)
        success, msg = verifier.verify_concrete_add(0x60, 0x10)
        self.assertTrue(success, f"Verification failed: {msg}")
    
    def test_verify_bytecode(self):
        """Test verification of bytecode."""
        verifier = TranslationVerifier(timeout_ms=10000, verbose=False)
        bytecode = bytes([0x60, 0x60, 0x60, 0x10, 0x01])
        success, msg = verifier.verify_bytecode(bytecode, 0x60, 0x10)
        self.assertTrue(success, f"Verification failed: {msg}")
    
    def test_verify_zero_add(self):
        """Test verification with zero values."""
        verifier = TranslationVerifier(timeout_ms=10000, verbose=False)
        success, msg = verifier.verify_concrete_add(0x00, 0x00)
        self.assertTrue(success, f"Verification failed: {msg}")
    
    def test_verify_max_values(self):
        """Test verification with max PUSH1 values."""
        verifier = TranslationVerifier(timeout_ms=10000, verbose=False)
        success, msg = verifier.verify_concrete_add(0xFF, 0xFF)
        self.assertTrue(success, f"Verification failed: {msg}")


if __name__ == '__main__':
    # Run tests with verbose output
    unittest.main(verbosity=2)

