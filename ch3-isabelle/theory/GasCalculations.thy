theory GasCalculations
  imports 
    EVM_types
    EVM_context
    EVM_network
    Params
    Utils
    uint256
begin

definition Csstore :: "uint256 \<Rightarrow> uint256 \<Rightarrow> int" where
  "Csstore orig newer = (if \<not>(newer = uint256_zero) \<and> (orig = uint256_zero) then Gsset else Gsreset)"

definition Gsload :: "network \<Rightarrow> int" where 
  "Gsload n = (if at_least_eip150 n then 200 else 50)"

definition Gsuicide :: "network \<Rightarrow> int" where 
  "Gsuicide n = (if at_least_eip150 n then 5000 else 0)"

definition Gcall :: "network \<Rightarrow> int" where 
  "Gcall net = (if at_least_eip150 net then 700 else 40)"

definition Gexpbyte :: "network \<Rightarrow> int" where 
  "Gexpbyte net = (if at_least_eip150 net then 50 else 10)"

definition Gselfdestruct :: "network \<Rightarrow> bool \<Rightarrow> int" where
"Gselfdestruct net is_empty = (
  if at_least_cancun net then 
    if is_empty then 5000 else 2300
  else Gsuicide net)"

definition calcMemSize64WithUint :: "uint256 \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"calcMemSize64WithUint off_set len = (
  if len = uint256_zero then CalculationSuccess 0
  else if \<not>(Isuint64 off_set) then CalcFailureReason GasUintOverflow
  else let val = (uint256_add off_set len)
       in if \<not>(Isuint64 val) then CalcFailureReason GasUintOverflow
          else CalculationSuccess (uint256_to_int val))"

definition calcMemSize64 :: "uint256 \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"calcMemSize64 offset len = (
  if \<not>(Isuint64 len)then CalcFailureReason GasUintOverflow
  else calcMemSize64WithUint offset len)"

fun new_memory_consumption :: "inst \<Rightarrow> int \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
  "new_memory_consumption (Arith KECCAK256) _ s0 s1 _ _ _ _ _ = calcMemSize64 s0 s1" |
  "new_memory_consumption (Memory CALLDATACOPY) _ s0 _ s2 _ _ _ _ = calcMemSize64 s0 s2" |
  "new_memory_consumption (Memory CODECOPY) _ s0 _ s2 _ _ _ _ = calcMemSize64 s0 s2" |
  "new_memory_consumption (Memory EXTCODECOPY) _ _ s1 _ s3 _ _ _ = calcMemSize64 s1 s3" |
  "new_memory_consumption (Memory MLOAD) _ s0 _ _ _ _ _ _ = calcMemSize64WithUint s0 \<lparr> z0 = 32, z1 = 0, z2 = 0, z3 = 0 \<rparr>" |
  "new_memory_consumption (Memory MSTORE) _ s0 _ _ _ _ _ _ = calcMemSize64WithUint s0 \<lparr> z0 = 32, z1 = 0, z2 = 0, z3 = 0 \<rparr>" |
  "new_memory_consumption (Memory MSTORE8) _ s0 _ _ _ _ _ _ = calcMemSize64WithUint s0 \<lparr> z0 = 1, z1 = 0, z2 = 0, z3 = 0 \<rparr>" |
  "new_memory_consumption (Memory MCOPY) _ s0 s1 s2 _ _ _ _ = (
    let mStart = (if s1 >\<^sub>u s0 then s1 else s0)
    in calcMemSize64 mStart s2)" |
  "new_memory_consumption (Memory RETURNDATACOPY) _ s0 _ s2 _ _ _ _ = calcMemSize64 s0 s2" |
  "new_memory_consumption (Misc CREATE) _ _ s1 s2 _ _ _ _ = calcMemSize64 s1 s2" |
  "new_memory_consumption (Misc CREATE2) _ _ s1 s2 _ _ _ _ = calcMemSize64 s1 s2" |
  "new_memory_consumption (Misc CALL) _ _ _ _ s3 s4 s5 s6 = (
    case calcMemSize64 s5 s6 of
      CalcFailureReason r \<Rightarrow> CalcFailureReason r
    | CalculationSuccess x \<Rightarrow> (
        case calcMemSize64 s3 s4 of
          CalcFailureReason r \<Rightarrow> CalcFailureReason r
        | CalculationSuccess y \<Rightarrow> CalculationSuccess (max x y)))" |
  "new_memory_consumption (Misc CALLCODE) _ _ _ _ s3 s4 s5 s6 = (
    case calcMemSize64 s5 s6 of
      CalcFailureReason r \<Rightarrow> CalcFailureReason r
    | CalculationSuccess x \<Rightarrow> (
        case calcMemSize64 s3 s4 of
          CalcFailureReason r \<Rightarrow> CalcFailureReason r
        | CalculationSuccess y \<Rightarrow> CalculationSuccess (max x y)))" |
  "new_memory_consumption (Misc DELEGATECALL) _ _ _ s2 s3 s4 s5 _ = (
    case calcMemSize64 s4 s5 of
      CalcFailureReason r \<Rightarrow> CalcFailureReason r
    | CalculationSuccess x \<Rightarrow> (
        case calcMemSize64 s2 s3 of
          CalcFailureReason r \<Rightarrow> CalcFailureReason r
        | CalculationSuccess y \<Rightarrow> CalculationSuccess (max x y)))" |
  "new_memory_consumption (Misc STATICCALL) _ _ _ s2 s3 s4 s5 _ = (
    case calcMemSize64 s4 s5 of
      CalcFailureReason r \<Rightarrow> CalcFailureReason r
    | CalculationSuccess x \<Rightarrow> (
        case calcMemSize64 s2 s3 of
          CalcFailureReason r \<Rightarrow> CalcFailureReason r
        | CalculationSuccess y \<Rightarrow> CalculationSuccess (max x y)))" |
  "new_memory_consumption (Misc RETURN) _ s0 s1 _ _ _ _ _ = calcMemSize64 s0 s1" |
  "new_memory_consumption (Misc REVERT) _ s0 s1 _ _ _ _ _ = calcMemSize64 s0 s1" |
  "new_memory_consumption (Log _) _ s0 s1 _ _ _ _ _ = calcMemSize64 s0 s1" |
  "new_memory_consumption _ orig_mem_usage _ _ _ _ _ _ _ = CalculationSuccess orig_mem_usage"

definition Cnew :: "uint256 \<Rightarrow> bool \<Rightarrow> int" where
  "Cnew value1 emp = (if emp then Gnewaccount else 0)"

definition Cxfer :: "uint256 \<Rightarrow> int" where
  "Cxfer value1 = (if value1 =\<^sub>u uint256_zero then 0 else Gcallvalue)"

definition Cextra :: "uint256 \<Rightarrow> bool \<Rightarrow> network \<Rightarrow> int" where
  "Cextra value1 emp net = (Gcall net + Cxfer value1 + Cnew value1 emp)"

definition L :: "int \<Rightarrow> int" where
  "L x = x - (x div 64)"

definition Cgascap :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> network \<Rightarrow> int \<Rightarrow> int" where
  "Cgascap mu0 mu2 emp remaining_gas net memu_extra = (
    if remaining_gas \<ge> (Cextra mu2 emp net + memu_extra) then
      min (L (remaining_gas - Cextra mu2 emp net - memu_extra)) (uint256_to_int mu0)
    else uint256_to_int mu0)"

definition Ccallgas :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> network \<Rightarrow> calculation_result \<Rightarrow> calculation_result" where
  "Ccallgas mu0 mu1 mu2 emp remaining_gas net memu_extra = (
    case memu_extra of
      CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
    | CalculationSuccess extra \<Rightarrow>
        let call_gas = (if at_least_eip150 net 
                       then Cgascap mu0 mu2 emp remaining_gas net extra 
                       else uint256_to_int mu0) + 
                      (if mu2 =\<^sub>u uint256_zero then 0 else Gcallstipend)
        in if call_gas < 0 
           then CalcFailureReason GasUintOverflow
           else CalculationSuccess call_gas)"

definition Ccall :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> network \<Rightarrow> calculation_result \<Rightarrow> calculation_result" where
  "Ccall mu0 mu1 mu2 emp remaining_gas net memu_extra = (
    case memu_extra of
      CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
    | CalculationSuccess extra \<Rightarrow>
        let call_gas = (if at_least_eip150 net 
                       then Cgascap mu0 mu2 emp remaining_gas net extra 
                       else (uint256_to_int mu0)) + 
                      Cextra mu2 emp net
        in if call_gas < 0 
           then CalcFailureReason GasUintOverflow
           else CalculationSuccess call_gas)"

definition Cmem :: "int \<Rightarrow> int" where
  "Cmem a = (if a = 0 then 0 else
    let words = toWordSize a;
        square = words * words;
        linCoef = words * MemoryGas;
        quadCoef = square div QuadCoeffDiv
    in linCoef + quadCoef)"

definition calc_memory_expansion_cost :: "int \<Rightarrow> int \<Rightarrow> calculation_result" where
"calc_memory_expansion_cost old_size new_size = (
  if new_size = 0 then 
    CalculationSuccess 0
  else if new_size > 0x1FFFFFFFE0 then 
    CalcFailureReason GasUintOverflow
  else if new_size \<le> old_size then 
    CalculationSuccess 0
  else 
    let new_words = toWordSize new_size;
        new_size_bytes = new_words * 32;
        square = new_words * new_words;
        lin_coef = new_words * MemoryGas;
        quad_coef = square div QuadCoeffDiv;
        new_total_fee = lin_coef + quad_coef;

        old_total_fee = Cmem old_size;
        fee = new_total_fee - old_total_fee

    in if fee < 0 then 
         CalcFailureReason GasUintOverflow
       else 
         CalculationSuccess fee)"

definition memory_expansion_cost :: "inst \<Rightarrow> variable_ctx \<Rightarrow> calculation_result" where
"memory_expansion_cost inst v = (
  let old_size = vctx_memory_usage v
  in case new_memory_consumption inst old_size 
        (vctx_stack_default 0 v) (vctx_stack_default 1 v)
        (vctx_stack_default 2 v) (vctx_stack_default 3 v)
        (vctx_stack_default 4 v) (vctx_stack_default 5 v)
        (vctx_stack_default 6 v) of
       CalcFailureReason r \<Rightarrow> CalcFailureReason r
     | CalculationSuccess new_size \<Rightarrow> calc_memory_expansion_cost old_size new_size)"

definition memory_copier_gas :: "variable_ctx \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"memory_copier_gas v stack_pos len = (
  if \<not>(Isuint64 len) then
    CalcFailureReason GasUintOverflow
  else
    let words = toWordSize (uint256_to_int len);
        copy_gas = words * Gcopy
    in if copy_gas \<ge> 2^64 then
          CalcFailureReason GasUintOverflow
        else 
          CalculationSuccess copy_gas)"

definition Csuicide :: "bool \<Rightarrow> network \<Rightarrow> int" where
  "Csuicide recipient_empty net = (Gsuicide net + (if recipient_empty \<and> at_least_eip150 net then Gnewaccount else 0))"

definition handle_memory_expansion_gas :: "variable_ctx \<Rightarrow> inst \<Rightarrow> int \<Rightarrow> calculation_result" where
"handle_memory_expansion_gas v inst base_gas = (
  case memory_expansion_cost inst v of
    CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
  | CalculationSuccess mem_gas \<Rightarrow>
      let dynamic_gas = mem_gas
      in if dynamic_gas \<ge> 2^64 then CalcFailureReason GasUintOverflow
          else CalculationSuccess (base_gas + dynamic_gas))"

definition handle_memory_copy_gas :: "variable_ctx \<Rightarrow> inst \<Rightarrow> int \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"handle_memory_copy_gas v inst base_gas stack_pos len = (
  case memory_expansion_cost inst v of
    CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
  | CalculationSuccess mem_gas \<Rightarrow> (
      case memory_copier_gas v stack_pos len of
        CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
      | CalculationSuccess copy_gas \<Rightarrow>
          let dynamic_gas = mem_gas + copy_gas
          in if dynamic_gas \<ge> 2^64 then CalcFailureReason GasUintOverflow
              else CalculationSuccess (base_gas + dynamic_gas)))"

(* todo: combine the handle_memory_copy_gas and handle_sha3_gas *)
definition handle_sha3_gas :: "variable_ctx \<Rightarrow> inst \<Rightarrow> int \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"handle_sha3_gas v inst base_gas len = (
  case memory_expansion_cost inst v of
    CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
  | CalculationSuccess mem_gas \<Rightarrow>
      if \<not>(Isuint64 len) then
        CalcFailureReason GasUintOverflow
      else 
        let words = toWordSize (uint256_to_int len);
            word_gas = words * Gsha3word
        in if word_gas \<ge> 2^64 then
             CalcFailureReason GasUintOverflow
           else if mem_gas + word_gas \<ge> 2^64 then CalcFailureReason GasUintOverflow
           else CalculationSuccess (base_gas + mem_gas + word_gas))"

definition handle_log_gas :: "variable_ctx \<Rightarrow> inst \<Rightarrow> int \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"handle_log_gas v inst n_topics requestedSize = (
  if \<not>(Isuint64 requestedSize) then
    CalcFailureReason GasUintOverflow
  else
    case memory_expansion_cost inst v of
      CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
    | CalculationSuccess mem_gas \<Rightarrow>
        let base_gas = Glog;
            topic_gas = n_topics * Glogtopic;
            data_gas = uint256_to_int requestedSize * Glogdata
        in 
        if base_gas + mem_gas \<ge> 2^64 then 
          CalcFailureReason GasUintOverflow
        else if base_gas + mem_gas + topic_gas \<ge> 2^64 then
          CalcFailureReason GasUintOverflow  
        else if data_gas \<ge> 2^64 then
          CalcFailureReason GasUintOverflow
        else if base_gas + mem_gas + topic_gas + data_gas \<ge> 2^64 then
          CalcFailureReason GasUintOverflow
        else 
          CalculationSuccess (base_gas + mem_gas + topic_gas + data_gas))"

definition handle_create_gas :: "variable_ctx \<Rightarrow> inst \<Rightarrow> int \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"handle_create_gas v inst base_gas in_size = (
  case memory_expansion_cost inst v of
    CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
  | CalculationSuccess mem_gas \<Rightarrow>
      if \<not>(Isuint64 in_size) then
        CalcFailureReason GasUintOverflow
      else if uint256_to_int in_size > MaxInitCodeSize then
        CalcFailureReason MaxInitCodeSizeExceeded
      else
        let words = (uint256_to_int in_size + 31) div 32;
            init_code_gas = words * Ginitcodeword
        in if mem_gas + init_code_gas \<ge> 2^64 then
             CalcFailureReason GasUintOverflow
           else CalculationSuccess (base_gas + mem_gas + init_code_gas))"

definition handle_create2_gas :: "variable_ctx \<Rightarrow> inst \<Rightarrow> int \<Rightarrow> uint256 \<Rightarrow> calculation_result" where
"handle_create2_gas v inst base_gas in_size = (
  case memory_expansion_cost inst v of
    CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
  | CalculationSuccess mem_gas \<Rightarrow>
      if \<not>(Isuint64 in_size) then
        CalcFailureReason GasUintOverflow
      else if uint256_to_int in_size > MaxInitCodeSize then
        CalcFailureReason MaxInitCodeSizeExceeded
      else
        let words = (uint256_to_int in_size + 31) div 32;
            init_code_gas = words * (Ginitcodeword + Gsha3word)
        in if mem_gas + init_code_gas \<ge> 2^64 then
             CalcFailureReason GasUintOverflow
           else CalculationSuccess (base_gas + mem_gas + init_code_gas))"

end
