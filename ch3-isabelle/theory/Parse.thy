theory Parse

imports 
  Main 
  "HOL-Data_Structures.AVL_Map"
  "EVM_syntax" 
  "EVMCommType"

begin

datatype parse_byte_result =
  Complete inst
| Incomplete nat

abbreviation "push n == Incomplete n"

definition parse_byte :: "byte \<Rightarrow> parse_byte_result"
where
"parse_byte =
  (\<lambda> b. Complete (Unknown b))
  ( 0x00 := Complete (Misc STOP)
  , 0x01 := Complete (Arith ADD)
  , 0x02 := Complete (Arith MUL)
  , 0x03 := Complete (Arith SUB)
  , 0x04 := Complete (Arith DIV)
  , 0x05 := Complete (Sarith SDIV)
  , 0x06 := Complete (Arith MOD)
  , 0x07 := Complete (Sarith SMOD)
  , 0x08 := Complete (Arith ADDMOD)
  , 0x09 := Complete (Arith MULMOD)
  , 0x0a := Complete (Arith EXP)
  , 0x0b := Complete (Sarith SIGNEXTEND)
  , 0x10 := Complete (Arith inst_LT)
  , 0x11 := Complete (Arith inst_GT)
  , 0x12 := Complete (Sarith SLT)
  , 0x13 := Complete (Sarith SGT)
  , 0x14 := Complete (Arith inst_EQ)
  , 0x15 := Complete (Arith ISZERO)
  , 0x16 := Complete (Bits inst_AND)
  , 0x17 := Complete (Bits inst_OR)
  , 0x18 := Complete (Bits inst_XOR)
  , 0x19 := Complete (Bits inst_NOT)
  , 0x1a := Complete (Bits BYTE)
  , 0x1b := Complete (Bits inst_SHL)
  , 0x1c := Complete (Bits inst_SHR)
  , 0x1d := Complete (Bits inst_SAR)
  , 0x20 := Complete (Arith KECCAK256)
  , 0x30 := Complete (Info ADDRESS)
  , 0x31 := Complete (Info BALANCE)
  , 0x32 := Complete (Info ORIGIN)
  , 0x33 := Complete (Info CALLER)
  , 0x34 := Complete (Info CALLVALUE)
  , 0x35 := Complete (Stack CALLDATALOAD)
  , 0x36 := Complete (Info CALLDATASIZE)
  , 0x37 := Complete (Memory CALLDATACOPY)
  , 0x38 := Complete (Info CODESIZE)
  , 0x39 := Complete (Memory CODECOPY)
  , 0x3a := Complete (Info GASPRICE)
  , 0x3b := Complete (Info EXTCODESIZE)
  , 0x3c := Complete (Memory EXTCODECOPY)
  , 0x3d := Complete (Info RETURNDATASIZE)
  , 0x3e := Complete (Memory RETURNDATACOPY)
  , 0x3f := Complete (Info EXTCODEHASH)
  , 0x40 := Complete (Info BLOCKHASH)
  , 0x41 := Complete (Info COINBASE)
  , 0x42 := Complete (Info TIMESTAMP)
  , 0x43 := Complete (Info NUMBER)
  , 0x44 := Complete (Info DIFFICULTY)
  , 0x45 := Complete (Info GASLIMIT)
  , 0x46 := Complete (Info CHAINID)
  , 0x47 := Complete (Info SELFBALANCE)
  , 0x48 := Complete (Info BASEFEE)
  , 0x49 := Complete (Info BLOBHASH)
  , 0x4a := Complete (Info BLOBBASEFEE)
  , 0x50 := Complete (Stack POP)
  , 0x51 := Complete (Memory MLOAD)
  , 0x52 := Complete (Memory MSTORE)
  , 0x53 := Complete (Memory MSTORE8)
  , 0x54 := Complete (Storage SLOAD)
  , 0x55 := Complete (Storage SSTORE)
  , 0x56 := Complete (Pc JUMP)
  , 0x57 := Complete (Pc JUMPI)
  , 0x58 := Complete (Pc PC)
  , 0x59 := Complete (Memory MSIZE)
  , 0x5a := Complete (Info GAS)
  , 0x5b := Complete (Pc JUMPDEST)
  , 0x5c := Complete (Memory TLOAD)
  , 0x5d := Complete (Memory TSTORE)
  , 0x5e := Complete (Memory MCOPY)
  , 0x5f := Complete (Stack PUSH0)
  , 0x60 := push 1
  , 0x61 := push 2
  , 0x62 := push 3
  , 0x63 := push 4
  , 0x64 := push 5
  , 0x65 := push 6
  , 0x66 := push 7
  , 0x67 := push 8
  , 0x68 := push 9
  , 0x69 := push 10
  , 0x6a := push 11
  , 0x6b := push 12
  , 0x6c := push 13
  , 0x6d := push 14
  , 0x6e := push 15
  , 0x6f := push 16
  , 0x70 := push 17
  , 0x71 := push 18
  , 0x72 := push 19
  , 0x73 := push 20
  , 0x74 := push 21
  , 0x75 := push 22
  , 0x76 := push 23
  , 0x77 := push 24
  , 0x78 := push 25
  , 0x79 := push 26
  , 0x7a := push 27
  , 0x7b := push 28
  , 0x7c := push 29
  , 0x7d := push 30
  , 0x7e := push 31
  , 0x7f := push 32
  , 0x80 := Complete (Dup 0)
  , 0x81 := Complete (Dup 1)
  , 0x82 := Complete (Dup 2)
  , 0x83 := Complete (Dup 3)
  , 0x84 := Complete (Dup 4)
  , 0x85 := Complete (Dup 5)
  , 0x86 := Complete (Dup 6)
  , 0x87 := Complete (Dup 7)
  , 0x88 := Complete (Dup 8)
  , 0x89 := Complete (Dup 9)
  , 0x8a := Complete (Dup 10)
  , 0x8b := Complete (Dup 11)
  , 0x8c := Complete (Dup 12)
  , 0x8d := Complete (Dup 13)
  , 0x8e := Complete (Dup 14)
  , 0x8f := Complete (Dup 15)
  , 0x90 := Complete (Swap 0)
  , 0x91 := Complete (Swap 1)
  , 0x92 := Complete (Swap 2)
  , 0x93 := Complete (Swap 3)
  , 0x94 := Complete (Swap 4)
  , 0x95 := Complete (Swap 5)
  , 0x96 := Complete (Swap 6)
  , 0x97 := Complete (Swap 7)
  , 0x98 := Complete (Swap 8)
  , 0x99 := Complete (Swap 9)
  , 0x9a := Complete (Swap 10)
  , 0x9b := Complete (Swap 11)
  , 0x9c := Complete (Swap 12)
  , 0x9d := Complete (Swap 13)
  , 0x9e := Complete (Swap 14)
  , 0x9f := Complete (Swap 15)
  , 0xa0 := Complete (Log LOG0)
  , 0xa1 := Complete (Log LOG1)
  , 0xa2 := Complete (Log LOG2)
  , 0xa3 := Complete (Log LOG3)
  , 0xa4 := Complete (Log LOG4)
  , 0xf0 := Complete (Misc CREATE)
  , 0xf1 := Complete (Misc CALL)
  , 0xf2 := Complete (Misc CALLCODE)
  , 0xf3 := Complete (Misc RETURN)
  , 0xf4 := Complete (Misc DELEGATECALL)
  , 0xf5 := Complete (Misc CREATE2)
  , 0xfa := Complete (Misc STATICCALL)
  , 0xfd := Complete (Misc REVERT)
  , 0xfe := Complete (Misc INVALID)
  , 0xff := Complete (Misc SELFDESTRUCT)
  )"

value "parse_byte 0xa8"

fun parse_bytes :: "byte list \<Rightarrow> inst list" where
  "parse_bytes [] = []" 
| "parse_bytes (b # rest) =
   (case parse_byte b of
     Complete i \<Rightarrow> i # (parse_bytes rest)
   | Incomplete n \<Rightarrow> (Stack (PUSH_N (take n rest))) # (parse_bytes (drop n rest))
   )"

value "parse_bytes [0x60, 0x60, 0x60, 0x40]"

definition integer_of_hex_char :: "char \<Rightarrow> integer"
where
"integer_of_hex_char c =
   (if integer_of_char c \<ge> 48 \<and> integer_of_char c < 58 then
      integer_of_char c - 48
    else if integer_of_char c \<ge> 97 \<and> integer_of_char c < 103 then
      integer_of_char c - 87
    else 0
   )"

declare integer_of_hex_char_def [simp]

value "integer_of_hex_char (CHR ''0'')"

fun bytes_of_hex_content :: "char list \<Rightarrow> byte list"
where
"bytes_of_hex_content [] = []" |
"bytes_of_hex_content [m] = []" |
"bytes_of_hex_content (m # n # rest) = 
  (word_of_int (int_of_integer ((integer_of_hex_char m) * 16 + integer_of_hex_char n)) # bytes_of_hex_content rest)"

(* ''0x'' prefix is optional *)
abbreviation parse_bytecode :: "char list \<Rightarrow> inst list" where
"parse_bytecode c == parse_bytes (bytes_of_hex_content 
  (if length c \<ge> 2 \<and> hd c = CHR ''0'' \<and> hd (tl c) = CHR ''x'' 
   then drop 2 c 
   else c))"

lemma parse_bytecode_6060:
  "parse_bytecode ''6060'' = parse_bytecode ''0x6060''"
  by eval
  
lemma parse_byte_111:
  "parse_byte 111 = push 16"
  unfolding parse_byte_def by simp

lemma parse_bytes_example:
  "parse_bytes [111, 200, 75, 166, 188, 149, 72, 64, 8, 246, 54, 47, 147, 22, 14, 243, 229, 99] =
   [Stack (PUSH_N [200, 75, 166, 188, 149, 72, 64, 8, 246, 54, 47, 147, 22, 14, 243, 229]), Stack (PUSH_N [])]"
  by eval

lemma parse_bytecode_example:
  "parse_bytecode ''0x6060604052600035900463ffffffff168063dffeadd014603a575b5b34156041575b6047'' = [
    Stack (PUSH_N [96]),              Stack (PUSH_N [64]),              \<comment>\<open>60 60, 60 40\<close>
    Memory MSTORE,                    Stack (PUSH_N [0]),               \<comment>\<open>52, 60 00\<close>
    Stack CALLDATALOAD,               Swap 0,                           \<comment>\<open>35, 90\<close>
    Arith DIV,                        Stack (PUSH_N [255,255,255,255]), \<comment>\<open>04, 63 ffffffff\<close>
    Bits inst_AND,                    Dup 0,                            \<comment>\<open>16, 80\<close>
    Stack (PUSH_N [223,254,173,208]), Arith inst_EQ,                    \<comment>\<open>63 dffeadd0, 14\<close>
    Stack (PUSH_N [58]),              Pc JUMPI,                         \<comment>\<open>60 3a, 57\<close>
    Pc JUMPDEST,                      Pc JUMPDEST,                      \<comment>\<open>5b, 5b\<close>
    Info CALLVALUE,                   Arith ISZERO,                     \<comment>\<open>34, 15\<close>
    Stack (PUSH_N [65]),              Pc JUMPI,                         \<comment>\<open>60 41, 57\<close>
    Pc JUMPDEST,                      Stack (PUSH_N [71])               \<comment>\<open>5b, 60 47\<close>
  ]"
    by eval


(* Converting Program to Mapping *)

subsection \<open>Converting Program to Mapping\<close>

fun store_byte_list_in_program ::
  "int  \<Rightarrow> byte list  \<Rightarrow>
   (int * inst) tree_ht   \<Rightarrow>
   (int * inst) tree_ht "
where
  "store_byte_list_in_program _ [] orig = orig"
| "store_byte_list_in_program pos (h # t) orig =
     store_byte_list_in_program (pos + 1) t (update pos (Unknown h) orig)"


fun program_avl_of_lst ::
  "int  \<Rightarrow> inst list 
   \<Rightarrow> (int * inst) tree_ht "
where
  "program_avl_of_lst _ [] = Leaf"
| "program_avl_of_lst pos (Stack (PUSH_N bytes) # rest) =
   store_byte_list_in_program (pos + 1) bytes 
   (update pos (Stack (PUSH_N bytes))
          (program_avl_of_lst (pos + 1 + (int (length bytes))) rest))"
| "program_avl_of_lst pos (i # rest) =
   update pos i (program_avl_of_lst (pos + 1) rest)"
  
abbreviation program_content_of_lst :: "inst list \<Rightarrow> (int \<Rightarrow> inst option)"
where
"program_content_of_lst lst \<equiv>
   (lookup (program_avl_of_lst 0 lst))"

declare update.simps [simp del]
declare lookup.simps [simp del]

end