theory EVM_syntax
  imports
    Main
    EVMCommType EVM_state
begin

definition byteFromNat  :: " nat \<Rightarrow> u8"  where 
  "byteFromNat n = of_int (int n)"

datatype bits_inst =
  inst_AND | inst_OR | inst_XOR | inst_NOT | BYTE | inst_SHL | inst_SHR | inst_SAR
   
fun bits_inst_code  :: "bits_inst \<Rightarrow> u8"  where 
  "bits_inst_code inst_AND  = 0x16"
| "bits_inst_code inst_OR   = 0x17"
| "bits_inst_code inst_XOR  = 0x18"
| "bits_inst_code inst_NOT  = 0x19"
| "bits_inst_code BYTE   = 0x1a"
| "bits_inst_code inst_SHL = 0x1b"
| "bits_inst_code inst_SHR = 0x1c"
| "bits_inst_code inst_SAR = 0x1d"

fun bits_stack_nums  :: "bits_inst \<Rightarrow> int*int"  where 
  "bits_stack_nums inst_AND = (2, 1)"
| "bits_stack_nums inst_OR  = (2, 1)"
| "bits_stack_nums inst_XOR = (2, 1)"
| "bits_stack_nums inst_NOT = (1, 1)"
| "bits_stack_nums BYTE  = (2, 1)"
| "bits_stack_nums inst_SHL = (2, 1)"
| "bits_stack_nums inst_SHR = (2, 1)"
| "bits_stack_nums inst_SAR = (2, 1)"

datatype sarith_inst =  
  SDIV | SMOD | SGT | SLT | SIGNEXTEND 

fun sarith_inst_code  :: "sarith_inst \<Rightarrow> u8"  where 
  "sarith_inst_code SDIV = 0x05"
| "sarith_inst_code SMOD = 0x07"
| "sarith_inst_code SGT =  0x13"
| "sarith_inst_code SLT =  0x12"
| "sarith_inst_code SIGNEXTEND = 0x0b"

fun sarith_inst_nums  :: "sarith_inst \<Rightarrow> int*int"  where 
  "sarith_inst_nums SDIV = (2, 1)"
| "sarith_inst_nums SMOD = (2, 1)"  
| "sarith_inst_nums SGT = (2, 1)"
| "sarith_inst_nums SLT = (2, 1)"
| "sarith_inst_nums SIGNEXTEND = (2, 1)"

datatype arith_inst = ADD | MUL | SUB | DIV | MOD | ADDMOD | MULMOD | EXP | inst_GT | inst_EQ | inst_LT | ISZERO | KECCAK256

fun arith_inst_code  :: "arith_inst \<Rightarrow> u8 "  where 
  "arith_inst_code ADD = 0x01"
| "arith_inst_code MUL = 0x02"
| "arith_inst_code SUB = 0x03"
| "arith_inst_code DIV = 0x04"           
| "arith_inst_code MOD = 0x06"
| "arith_inst_code ADDMOD = 0x08"
| "arith_inst_code MULMOD = 0x09"
| "arith_inst_code EXP = 0x0a"
| "arith_inst_code inst_GT = 0x11"
| "arith_inst_code inst_LT = 0x10"
| "arith_inst_code inst_EQ = 0x14"
| "arith_inst_code ISZERO = 0x15"
| "arith_inst_code KECCAK256 = 0x20"

fun arith_inst_numbers  :: "arith_inst \<Rightarrow> int*int"  where 
  "arith_inst_numbers ADD = (2, 1)"
| "arith_inst_numbers MUL = (2, 1)"
| "arith_inst_numbers SUB = (2, 1)"
| "arith_inst_numbers DIV = (2, 1)"
| "arith_inst_numbers MOD = (2, 1)"
| "arith_inst_numbers ADDMOD = (3, 1)"
| "arith_inst_numbers MULMOD = (3, 1)"
| "arith_inst_numbers EXP = (2, 1)"
| "arith_inst_numbers inst_GT = (2, 1)"
| "arith_inst_numbers inst_LT = (2, 1)"
| "arith_inst_numbers inst_EQ = (2, 1)"
| "arith_inst_numbers ISZERO = (1, 1)"
| "arith_inst_numbers KECCAK256 = (2, 1)"

datatype info_inst = ADDRESS | BALANCE | ORIGIN | CALLER | CALLVALUE | CALLDATASIZE | CODESIZE |
 GASPRICE | EXTCODESIZE | BLOCKHASH | COINBASE | TIMESTAMP | NUMBER | DIFFICULTY | GASLIMIT | GAS | EXTCODEHASH | RETURNDATASIZE | CHAINID | SELFBALANCE | BASEFEE | BLOBHASH | BLOBBASEFEE

fun info_inst_code  :: "info_inst \<Rightarrow> u8"  where 
  "info_inst_code ADDRESS = 0x30"
| "info_inst_code BALANCE = 0x31"
| "info_inst_code ORIGIN = 0x32"
| "info_inst_code CALLVALUE = 0x34"
| "info_inst_code CALLDATASIZE = 0x36"
| "info_inst_code CALLER = 0x33"
| "info_inst_code CODESIZE = 0x38"
| "info_inst_code GASPRICE = 0x3a"
| "info_inst_code EXTCODESIZE = 0x3b"
| "info_inst_code BLOCKHASH = 0x40"
| "info_inst_code COINBASE = 0x41"
| "info_inst_code TIMESTAMP = 0x42"
| "info_inst_code NUMBER = 0x43"
| "info_inst_code DIFFICULTY = 0x44"
| "info_inst_code GASLIMIT = 0x45"
| "info_inst_code GAS = 0x5a"
| "info_inst_code EXTCODEHASH = 0x3f"
| "info_inst_code RETURNDATASIZE = 0x3d"
| "info_inst_code CHAINID = 0x46"
| "info_inst_code SELFBALANCE = 0x47"
| "info_inst_code BASEFEE = 0x48"
| "info_inst_code BLOBHASH = 0x49"
| "info_inst_code BLOBBASEFEE = 0x4a"

fun info_inst_numbers  :: "info_inst \<Rightarrow> int*int"  where 
  "info_inst_numbers ADDRESS = (0, 1)"
| "info_inst_numbers BALANCE = (1, 1)"
| "info_inst_numbers ORIGIN = (0, 1)"
| "info_inst_numbers CALLER = (0, 1)"
| "info_inst_numbers CALLVALUE = (0, 1)"
| "info_inst_numbers CALLDATASIZE = (0, 1)"
| "info_inst_numbers CODESIZE = (0, 1)"
| "info_inst_numbers GASPRICE = (0, 1)"
| "info_inst_numbers EXTCODESIZE = (1, 1)"
| "info_inst_numbers BLOCKHASH = (1, 1)"
| "info_inst_numbers COINBASE = (0, 1)"  
| "info_inst_numbers TIMESTAMP = (0, 1)"
| "info_inst_numbers NUMBER = (0, 1)"
| "info_inst_numbers DIFFICULTY = (0, 1)"
| "info_inst_numbers GASLIMIT = (0, 1)"
| "info_inst_numbers GAS = (0, 1)"
| "info_inst_numbers EXTCODEHASH = (1, 1)"
| "info_inst_numbers RETURNDATASIZE = (0, 1)"
| "info_inst_numbers CHAINID = (0, 1)"
| "info_inst_numbers SELFBALANCE = (0, 1)"
| "info_inst_numbers BASEFEE = (0, 1)"
| "info_inst_numbers BLOBHASH = (1, 1)"
| "info_inst_numbers BLOBBASEFEE = (0, 1)"

type_synonym nibble = u4

type_synonym dup_inst =" nibble "

definition dup_inst_code  :: "u4 \<Rightarrow> u8 "  where 
  "dup_inst_code m = (word_of_int (uint m) +(word_of_int 0x80))" 

definition dup_inst_numbers  :: "u4 \<Rightarrow> int*int"  where 
  "dup_inst_numbers m = (uint m, (uint m + 1))" 

datatype memory_inst = MLOAD | MSTORE | MSTORE8 | CALLDATACOPY | CODECOPY | EXTCODECOPY | MSIZE | TLOAD | TSTORE | MCOPY | RETURNDATACOPY

fun memory_inst_code  :: "memory_inst \<Rightarrow> u8"  where 
  "memory_inst_code MLOAD = 0x51"
| "memory_inst_code MSTORE = 0x52"
| "memory_inst_code MSTORE8 = 0x53"
| "memory_inst_code CALLDATACOPY = 0x37"
| "memory_inst_code CODECOPY = 0x39"
| "memory_inst_code EXTCODECOPY = 0x3c"
| "memory_inst_code MSIZE = 0x59"
| "memory_inst_code TLOAD = 0x5c"
| "memory_inst_code TSTORE = 0x5d"
| "memory_inst_code MCOPY = 0x5e"
| "memory_inst_code RETURNDATACOPY = 0x3e"

fun memory_inst_numbers  :: "memory_inst \<Rightarrow> int*int"  where 
  "memory_inst_numbers MLOAD = (1, 1)"
| "memory_inst_numbers MSTORE = (2, 0)"
| "memory_inst_numbers MSTORE8 = (2, 0)"
| "memory_inst_numbers CALLDATACOPY = (3, 0)"
| "memory_inst_numbers CODECOPY = (3, 0)"
| "memory_inst_numbers EXTCODECOPY = (4, 0)"
| "memory_inst_numbers MSIZE = (0, 1)"
| "memory_inst_numbers TLOAD = (1, 1)"
| "memory_inst_numbers TSTORE = (2, 0)"
| "memory_inst_numbers MCOPY = (3, 0)"
| "memory_inst_numbers RETURNDATACOPY = (3, 0)"

datatype storage_inst =
  SLOAD | SSTORE 

fun storage_inst_code  :: "storage_inst \<Rightarrow> 8 word"  where 
  "storage_inst_code SLOAD = 0x54"
| "storage_inst_code SSTORE = 0x55"

fun storage_inst_numbers  :: "storage_inst \<Rightarrow> int*int"  where 
  "storage_inst_numbers SLOAD = (1, 1)"
| "storage_inst_numbers SSTORE = (2, 0)"

datatype pc_inst = JUMP | JUMPI | PC | JUMPDEST

fun pc_inst_code  :: "pc_inst \<Rightarrow> u8"  where 
  "pc_inst_code JUMP = 0x56"
| "pc_inst_code JUMPI = 0x57"
| "pc_inst_code PC = 0x58"
| "pc_inst_code JUMPDEST = 0x5b"

fun pc_inst_numbers  :: "pc_inst \<Rightarrow> int*int"  where 
  "pc_inst_numbers JUMP = (1, 0)"
| "pc_inst_numbers JUMPI = (2, 0)"
| "pc_inst_numbers PC = (0, 1)"
| "pc_inst_numbers JUMPDEST = (0, 0)"

datatype stack_inst = POP | PUSH_N "byte list" | CALLDATALOAD | PUSH0

fun stack_inst_code  :: "stack_inst \<Rightarrow> u8 list"  where
  "stack_inst_code POP = [0x50]"
| "stack_inst_code (PUSH_N lst) = (
    if List.length lst < 1 then [0x60, 0x00] \<comment> \<open>this case should not exist \<close>
    else if List.length lst > 32 then [0x60, 0x00] \<comment> \<open>this case should not exist \<close>
    else [byteFromNat (List.length lst)+ 0x5f] @ lst )" 
| "stack_inst_code CALLDATALOAD = [0x35]"
| "stack_inst_code PUSH0 = [0x5f]"

fun stack_inst_numbers  :: "stack_inst \<Rightarrow> int*int"  where 
  "stack_inst_numbers POP = (1, 0)"
| "stack_inst_numbers (PUSH_N _) = (0, 1)"
| "stack_inst_numbers CALLDATALOAD = (1, 1)"
| "stack_inst_numbers PUSH0 = (0, 1)"

type_synonym swap_inst =" nibble "

definition swap_inst_code  :: "u4 \<Rightarrow> u8"  where 
  "swap_inst_code m = word_of_int (uint m) +word_of_int 0x90" 

definition swap_inst_numbers  :: "4 word \<Rightarrow> int*int"  where 
  "swap_inst_numbers m = (uint m +1, uint m +1)" 

datatype log_inst =
  LOG0| LOG1| LOG2| LOG3| LOG4

definition int_of_log :: "log_inst \<Rightarrow> int" where
  "int_of_log l = (
    case l of
    LOG0 \<Rightarrow> 0 |
    LOG1 \<Rightarrow> 1 |
    LOG2 \<Rightarrow> 2 |
    LOG3 \<Rightarrow> 3 |
    LOG4 \<Rightarrow> 4
  )"

fun log_inst_code  :: "log_inst \<Rightarrow> u8 "  where 
  "log_inst_code LOG0 = 0xa0"         
| "log_inst_code LOG1 = 0xa1"
| "log_inst_code LOG2 = 0xa2"
| "log_inst_code LOG3 = 0xa3"
| "log_inst_code LOG4 = 0xa4"

fun log_inst_numbers  :: "log_inst \<Rightarrow> int*int"  where 
  "log_inst_numbers LOG0 = (2, 0)"
| "log_inst_numbers LOG1 = (3, 0)"        
| "log_inst_numbers LOG2 = (4, 0)"
| "log_inst_numbers LOG3 = (5, 0)"
| "log_inst_numbers LOG4 = (6, 0)"

datatype misc_inst = STOP | CREATE | CALL | CALLCODE | DELEGATECALL | RETURN | CREATE2 | STATICCALL | REVERT | INVALID | SELFDESTRUCT

fun misc_inst_code  :: "misc_inst \<Rightarrow> u8 "  where 
  "misc_inst_code STOP = 0x00"
| "misc_inst_code CREATE = 0xf0"
| "misc_inst_code CALL = 0xf1"
| "misc_inst_code CALLCODE = 0xf2"
| "misc_inst_code RETURN = 0xf3"
| "misc_inst_code DELEGATECALL = 0xf4"
| "misc_inst_code CREATE2 = 0xf5"
| "misc_inst_code STATICCALL = 0xfa"
| "misc_inst_code REVERT = 0xfd"
| "misc_inst_code INVALID = 0xfe"
| "misc_inst_code SELFDESTRUCT = 0xff"

fun misc_inst_numbers  :: "misc_inst \<Rightarrow> int*int"  where 
  "misc_inst_numbers STOP = (0, 0)"
| "misc_inst_numbers CREATE = (3, 1)"
| "misc_inst_numbers CALL = (7, 1)"
| "misc_inst_numbers CALLCODE = (7, 1)"
| "misc_inst_numbers RETURN = (2, 0)"
| "misc_inst_numbers DELEGATECALL = (6, 1)"
| "misc_inst_numbers CREATE2 = (4, 1)"
| "misc_inst_numbers STATICCALL = (6, 1)"
| "misc_inst_numbers REVERT = (2, 0)"
| "misc_inst_numbers INVALID = (0, 0)"
| "misc_inst_numbers SELFDESTRUCT = (1, 0)"

datatype inst =
     Unknown byte
  | Bits " bits_inst "
  | Sarith " sarith_inst "
  | Arith " arith_inst "
  | Info " info_inst "
  | Dup " dup_inst "
  | Memory " memory_inst "
  | Storage " storage_inst "
  | Pc pc_inst
  | Stack " stack_inst "
  | Swap " swap_inst "
  | Log " log_inst "
  | Misc " misc_inst "


fun maybe_to_list  :: "'a option \<Rightarrow> 'a list"  where 
  "maybe_to_list None = ( [])"
| "maybe_to_list (Some s) = ( [s])" 

fun inst_code  :: "inst \<Rightarrow>( 8 word)list"  where 
  "inst_code (Unknown b) = ( [b])" 
| "inst_code (Bits b) = ( [bits_inst_code b])" 
| "inst_code (Sarith s) = ( [sarith_inst_code s])" 
| "inst_code (Arith a) = ( [arith_inst_code a])"   
| "inst_code (Info i) = ( [info_inst_code i])" 
| "inst_code (Dup d) = ( [dup_inst_code d])" 
| "inst_code (Memory m) = ( [memory_inst_code m])" 
| "inst_code (Storage s) = ( [storage_inst_code s])" 
| "inst_code (Pc p) = ( [pc_inst_code p])" 
| "inst_code (Stack s) = ( stack_inst_code s )" 
| "inst_code (Swap s) = ( [swap_inst_code s])" 
| "inst_code (Log l) = ( [log_inst_code l])" 
| "inst_code (Misc m) = ( [misc_inst_code m])" 
  
fun inst_stack_numbers :: "inst \<Rightarrow> int * int" where 
  "inst_stack_numbers (Unknown _) = (0, 0)" |
  "inst_stack_numbers (Bits b) = bits_stack_nums b" |
  "inst_stack_numbers (Sarith s) = sarith_inst_nums s" |
  "inst_stack_numbers (Arith a) = arith_inst_numbers a" |
  "inst_stack_numbers (Info i') = info_inst_numbers i'" |
  "inst_stack_numbers (Dup d) = dup_inst_numbers d" |
  "inst_stack_numbers (Memory m) = memory_inst_numbers m" |
  "inst_stack_numbers (Storage s) = storage_inst_numbers s" |
  "inst_stack_numbers (Pc p) = pc_inst_numbers p" |
  "inst_stack_numbers (Stack s) = stack_inst_numbers s" |
  "inst_stack_numbers (Swap s) = swap_inst_numbers s" |
  "inst_stack_numbers (Log l) = log_inst_numbers l" |
  "inst_stack_numbers (Misc m) = misc_inst_numbers m"

definition inst_size :: "inst \<Rightarrow> int" where 
  "inst_size i = int (List.length (inst_code i))"

end