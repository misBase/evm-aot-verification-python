theory EVM_semantics
  imports
    EVM_types EVM_network EVM_state
    EVM_syntax EVM_context
    GasCalculations
    Utils Keccak Parse
begin

datatype instruction_result =
  InstructionContinue "variable_ctx" 
| InstructionToEnvironment "contract_action" "variable_ctx" "(int * int)option"

definition instruction_failure_result :: "variable_ctx \<Rightarrow> failure_reason list \<Rightarrow> instruction_result" where
  "instruction_failure_result v reasons = InstructionToEnvironment (ContractFail reasons) v None"

definition instruction_return_result :: "byte list \<Rightarrow> variable_ctx \<Rightarrow> instruction_result" where
  "instruction_return_result x v = InstructionToEnvironment (ContractReturn x) v None"

definition gas :: "variable_ctx \<Rightarrow> u256" where
  "gas v = word_of_int (vctx_gas v)"

definition M :: "int \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> int" where
  "M s f l = (if l = 0 then s else max s ((Word.uint f + Word.uint l + 31) div 32))"

definition stack_0_0_op :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "stack_0_0_op v c = InstructionContinue (vctx_advance_pc c v)"

definition stack_0_1_op :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> u256 \<Rightarrow> instruction_result" where
  "stack_0_1_op v c w = InstructionContinue (vctx_advance_pc c (v (| vctx_stack := w # vctx_stack v |)))"

definition stack_1_1_op :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> (u256 \<Rightarrow> u256) \<Rightarrow> instruction_result" where
  "stack_1_1_op v c f = (case vctx_stack v of
    [] \<Rightarrow> instruction_failure_result v [TooShortStack]
  | h # t \<Rightarrow> InstructionContinue (vctx_advance_pc c (v (| vctx_stack := f h # t |))))"

definition stack_2_1_op :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> (u256 \<Rightarrow> u256 \<Rightarrow> u256) \<Rightarrow> instruction_result" where
  "stack_2_1_op v c f = (case vctx_stack v of
    operand0 # operand1 # rest \<Rightarrow> InstructionContinue (vctx_advance_pc c (v (| vctx_stack := f operand0 operand1 # rest |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition stack_3_1_op :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> (u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256) \<Rightarrow> instruction_result" where
  "stack_3_1_op v c f = (case vctx_stack v of
    operand0 # operand1 # operand2 # rest \<Rightarrow> InstructionContinue (vctx_advance_pc c (v (| vctx_stack := f operand0 operand1 operand2 # rest |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"


definition sstore_refund :: "network \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> int" where
  "sstore_refund net original current new_value =
    (if at_least_london net then
       (if current = new_value then 0
        else if current = original then
          (if original = 0 then 0
           else if new_value = 0 then SstoreClearsScheduleRefundEIP3529 else 0)
        else
          (if original \<noteq> 0 then
             (if current = 0 then - SstoreClearsScheduleRefundEIP3529
              else if new_value = 0 then SstoreClearsScheduleRefundEIP3529 else 0)
           else 0)
          + (if original = new_value then
               (if original = 0 then SstoreResetClearRefundEIP2929
                else SstoreResetRefundEIP2929)
             else 0))
     else
       (if original \<noteq> 0 \<and> new_value = 0 then 15000 else 0))"

definition jump :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "jump v c = (case vctx_stack v of
    pos # tl1 \<Rightarrow>
      if Word.uint pos \<ge> 2^64 then
        instruction_failure_result v [InvalidJumpDestination]
      else
        let v_new = v (| vctx_stack := tl1, vctx_pc := Word.uint pos |)
        in (case vctx_next_instruction v_new c of
              Some (Pc JUMPDEST) \<Rightarrow> InstructionContinue v_new
            | _ \<Rightarrow> instruction_failure_result v [InvalidJumpDestination])
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition blockedInstructionContinue :: "variable_ctx \<Rightarrow> bool \<Rightarrow> instruction_result" where
  "blockedInstructionContinue v _ = InstructionContinue v"

definition blocked_jump :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> bool \<Rightarrow> instruction_result" where
  "blocked_jump v c _ = jump v c"

definition strict_if :: "bool \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> (bool \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "strict_if b x y = (if b then x True else y True)"

definition jumpi :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "jumpi v c = (case vctx_stack v of
    pos # cond # rest \<Rightarrow>
      let new_env = v (| vctx_stack := pos # rest |)
      in strict_if (cond = 0)
           (blockedInstructionContinue (vctx_advance_pc c (vctx_pop_stack 2 v)))
           (blocked_jump new_env c)
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition datasize :: "variable_ctx \<Rightarrow> u256" where
  "datasize v = word256FromNat (length (vctx_data_sent v))"

definition byte_list_fill_right :: "u8 \<Rightarrow> nat \<Rightarrow> u8 list \<Rightarrow> u8 list" where
  "byte_list_fill_right filled target orig = (
    if length orig \<ge> target then orig else
    let filling_len = target - length orig
    in orig @ replicate filling_len filled)"

definition constant_mark :: "byte list \<Rightarrow> byte list" where
  "constant_mark lst = lst"

definition read_word_from_bytes :: "nat \<Rightarrow> u8 list \<Rightarrow> u256" where
  "read_word_from_bytes idx lst = (
    if length lst \<le> idx then 0
    else word_rcat (byte_list_fill_right 0 32 (take 32 (drop idx lst))))"

definition cut_data :: "variable_ctx \<Rightarrow> u256 \<Rightarrow> u256" where
  "cut_data v idx = (
    if Word.uint idx < 2^64 then
      read_word_from_bytes (unat idx) (vctx_data_sent v)
    else 
      0)"

fun cut_natural_map :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> u8) \<Rightarrow> u8 list" where
  "cut_natural_map idx 0 nmap = []"
| "cut_natural_map idx (Suc n) nmap = nmap idx # cut_natural_map (idx + 1) n nmap"

definition vctx_next_instruction_default :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> inst" where
  "vctx_next_instruction_default v c = (case vctx_next_instruction v c of
      Some i \<Rightarrow> i
    | None \<Rightarrow> Misc STOP)"

definition vctx_recipient :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> 160 word" where
  "vctx_recipient v c = (case vctx_next_instruction_default v c of
    Misc SELFDESTRUCT \<Rightarrow> Word.ucast (vctx_stack_default 0 v)
  | Misc CALL \<Rightarrow> Word.ucast (vctx_stack_default 1 v)
  | Misc CALLCODE \<Rightarrow> cctx_this c
  | Misc DELEGATECALL \<Rightarrow> cctx_this c
  | Misc STATICCALL \<Rightarrow> Word.ucast (vctx_stack_default 1 v)
  | _ \<Rightarrow> 0)"

definition calc_memu_extra :: "int \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> calculation_result" where
  "calc_memu_extra orig_memory_usage s0 s1 s2 s3 s4 s5 s6 = 
    (case new_memory_consumption (Misc CALL) orig_memory_usage s0 s1 s2 s3 s4 s5 s6 of
      CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
    | CalculationSuccess new_size \<Rightarrow> 
        let mem_expansion = Cmem (max orig_memory_usage new_size) - Cmem orig_memory_usage
        in if mem_expansion < 0 
           then CalcFailureReason GasUintOverflow
           else CalculationSuccess mem_expansion)"

definition calc_memu_extra2 :: "variable_ctx \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> calculation_result" where
  "calc_memu_extra2 v s0 s1 s2 s3 s4 s5 s6 = 
    (case new_memory_consumption (Misc DELEGATECALL) (vctx_memory_usage v) s0 s1 s2 s3 s4 s5 s6 of
      CalcFailureReason reason \<Rightarrow> CalcFailureReason reason
    | CalculationSuccess new_size \<Rightarrow> 
        let mem_expansion = Cmem (max (vctx_memory_usage v) new_size) - Cmem (vctx_memory_usage v)
        in if mem_expansion < 0 
           then CalcFailureReason GasUintOverflow
           else CalculationSuccess mem_expansion)"

definition call :: "network \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "call net v c = (case vctx_stack v of
    g # r # value1 # in_begin # in_size # out_begin # out_size # rest \<Rightarrow>
      (case calc_memu_extra (vctx_memory_usage v) g r value1 in_begin in_size out_begin out_size of
        CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
      | CalculationSuccess memu_extra \<Rightarrow>
          (case Ccallgas v g r value1 (\<not> (vctx_account_existence v (vctx_recipient v c))) (vctx_gas v) net 
                (CalculationSuccess memu_extra) of
            CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
          | CalculationSuccess call_gas \<Rightarrow>
              InstructionToEnvironment
                (ContractCall
                  \<lparr> callarg_gas = word_of_int call_gas,
                    callarg_code = Word.ucast r,
                    callarg_recipient = Word.ucast r,
                    callarg_value = value1,
                    callarg_data = cut_memory in_begin in_size (vctx_memory v),
                    callarg_output_begin = out_begin,
                    callarg_output_size = out_size \<rparr>)
                (vctx_advance_pc c
                  (v \<lparr> vctx_stack := rest,
                       vctx_balance := update_balance (cctx_this c) (\<lambda>orig. orig - value1)
                                       (vctx_balance v) \<rparr>))
                (Some (Word.uint out_begin, Word.uint out_size))))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition delegatecall :: "network \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "delegatecall net v c = (case vctx_stack v of
    e0 # e1 # e3 # e4 # e5 # e6 # rest \<Rightarrow>
      (case calc_memu_extra2 v e0 e1 e3 e4 e5 e6 (vctx_stack_default 6 v) of
        CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
      | CalculationSuccess memu_extra \<Rightarrow>
          (case Ccallgas v e0 e1 0 (\<not> (vctx_account_existence v (vctx_recipient v c))) (vctx_gas v) net 
                (CalculationSuccess memu_extra) of
            CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
          | CalculationSuccess call_gas \<Rightarrow>
              InstructionToEnvironment
                (ContractDelegateCall
                  \<lparr> callarg_gas = word_of_int call_gas,
                    callarg_code = Word.ucast e1,
                    callarg_recipient = Word.ucast e1,
                    callarg_value = vctx_value_sent v,
                    callarg_data = cut_memory e3 e4 (vctx_memory v),
                    callarg_output_begin = e5,
                    callarg_output_size = e6 \<rparr>)
                (vctx_advance_pc c (v \<lparr> vctx_stack := rest \<rparr>))
                (Some (Word.uint e5, Word.uint e6))))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition callcode :: "network \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "callcode net v c = (case vctx_stack v of
    e0 # e1 # e2 # e3 # e4 # e5 # e6 # rest \<Rightarrow>
      (case calc_memu_extra (vctx_memory_usage v) e0 e1 e2 e3 e4 e5 e6 of
        CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
      | CalculationSuccess memu_extra \<Rightarrow>
          (case Ccallgas v e0 e1 e2 (\<not> (vctx_account_existence v (vctx_recipient v c))) (vctx_gas v) net 
                (CalculationSuccess memu_extra) of
            CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
          | CalculationSuccess call_gas \<Rightarrow>
              InstructionToEnvironment
                (ContractCall
                  \<lparr> callarg_gas = word_of_int call_gas,
                    callarg_code = Word.ucast e1,
                    callarg_recipient = cctx_this c,
                    callarg_value = e2,
                    callarg_data = cut_memory e3 e4 (vctx_memory v),
                    callarg_output_begin = e5,
                    callarg_output_size = e6 \<rparr>)
                (vctx_advance_pc c (v \<lparr> vctx_stack := rest \<rparr>))
                (Some (Word.uint e5, Word.uint e6))))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition create :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "create v c = (case vctx_stack v of
    vl # code_start # code_len # rest \<Rightarrow>
      let code = cut_memory code_start code_len (vctx_memory v)
      in InstructionToEnvironment (ContractCreate
           (| createarg_value = vl, createarg_code = code |))
           (vctx_advance_pc c (v (| vctx_stack := rest |)))
           (Some (0, 0))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition vctx_returned_bytes :: "variable_ctx \<Rightarrow> u8 list" where
  "vctx_returned_bytes v = (case vctx_stack v of
    e0 # e1 # _ \<Rightarrow> cut_memory e0 e1 (vctx_memory v)
  | _ \<Rightarrow> [])"

definition ret :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "ret v _ = (case vctx_stack v of
    _ # _ # _ \<Rightarrow> InstructionToEnvironment (ContractReturn (vctx_returned_bytes v)) v None
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition stop :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "stop v _ = InstructionToEnvironment (ContractReturn []) v None"

definition pop :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "pop v c = (case vctx_stack v of
    _ # tl1 \<Rightarrow> InstructionContinue (vctx_advance_pc c (v (| vctx_stack := tl1 |)))
  | [] \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition push0 :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"push0 v c = stack_0_1_op v c 0"

definition general_dup :: "u4 \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "general_dup n v c = (case index (vctx_stack v) (unat n) of
    None \<Rightarrow> instruction_failure_result v [TooShortStack]
  | Some duplicated \<Rightarrow> InstructionContinue (vctx_advance_pc c (v (| vctx_stack := duplicated # vctx_stack v |))))"

definition list_swap  :: \<open> nat \<Rightarrow> 'a list \<Rightarrow>('a list)option \<close>  where 
     \<open> list_swap n lst = ( (case  (index lst n, index lst 0) of
   (Some n_th, Some first1) => Some (List.concat [[n_th], List.take (n - 1 ) (List.drop( 1 ) lst), [first1], List.drop ( 1 + n) lst])
 | _ => None
))\<close> 

definition swap :: "nat \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "swap n v c = 
    (case list_swap (n + 1) (vctx_stack v) of
       None => instruction_failure_result v [TooShortStack]
     | Some new_stack => InstructionContinue (vctx_advance_pc c (v (| vctx_stack := new_stack |))))"

definition sstore :: "network \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "sstore net v c = (case vctx_stack v of
    addr # vl # stack_tail \<Rightarrow>
      let new_v = v (| vctx_stack := stack_tail,
                      vctx_touched_storage_index := addr # vctx_touched_storage_index v,
                      vctx_refund := vctx_refund v + sstore_refund net (vctx_storage_at_call v addr) (vctx_storage v addr) vl |)
      in InstructionContinue (vctx_advance_pc c (vctx_update_storage addr vl new_v))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition sload :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "sload v c = (case vctx_stack v of
    addr # rest \<Rightarrow>
      let new_v = v (| vctx_stack := vctx_storage v addr # rest,
                       vctx_touched_storage_index := addr # vctx_touched_storage_index v |)
      in InstructionContinue (vctx_advance_pc c new_v)
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition mload :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "mload v c = (case vctx_stack v of
    pos # rest \<Rightarrow>
      let value1 = read_word_from_bytes 0 (cut_memory pos 32 (vctx_memory v))
      in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := value1 # rest |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition store_byte_list_memory :: "u256 \<Rightarrow> u8 list \<Rightarrow> (u256 \<Rightarrow> u8) \<Rightarrow> u256 \<Rightarrow> u8" where
  "store_byte_list_memory pos lst orig p = (case index lst (unat (p - pos)) of
    Some e \<Rightarrow> e
  | None \<Rightarrow> orig p)"

definition store_word_memory :: "u256 \<Rightarrow> u256 \<Rightarrow> (w256 \<Rightarrow> byte) \<Rightarrow> w256 \<Rightarrow> byte" where
  "store_word_memory pos vl mem = store_byte_list_memory pos (word_rsplit vl) mem"

definition mstore :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "mstore v c = (case vctx_stack v of
    pos # vl # rest \<Rightarrow>
      let new_memory = store_word_memory pos vl (vctx_memory v)
      in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := rest, vctx_memory := new_memory |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition mstore8 :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "mstore8 v c = (case vctx_stack v of
    pos # vl # rest \<Rightarrow>
      let new_memory = (\<lambda>p. if p = pos then Word.ucast vl else vctx_memory v p)
      in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := rest, vctx_memory := new_memory |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition input_as_natural_map :: "u8 list \<Rightarrow> nat \<Rightarrow> u8" where
  "input_as_natural_map lst idx = (let idx = int idx in
    if idx < 0 then 0
    else if int (length lst) \<le> idx then 0
    else (case index lst (nat (abs idx)) of
      None \<Rightarrow> 0
    | Some a \<Rightarrow> a))"

definition calldatacopy :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "calldatacopy v c = (case vctx_stack v of
    dst_start # src_start # len # rest \<Rightarrow>
      let src_start64 = (if Word.uint src_start \<ge> 2^64 then 2^64 - 1 else Word.uint src_start);
          len64 = Word.uint len;
          dst_start64 = Word.uint dst_start;
          input_data = vctx_data_sent v;
          data = cut_natural_map (nat src_start64) (nat len64) (input_as_natural_map input_data);
          new_memory = store_byte_list_memory dst_start data (vctx_memory v)
      in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := rest, vctx_memory := new_memory |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition codecopy :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "codecopy v c = (case vctx_stack v of
    dst_start # src_start # len # rest \<Rightarrow>
      let src_start64 = (if Word.uint src_start \<ge> 2^64 then 2^64 - 1 else Word.uint src_start);
          len64 = Word.uint len;
          data = cut_natural_map (nat src_start64) (nat len64) (program_as_natural_map (cctx_program c))
      in let new_memory = store_byte_list_memory dst_start data (vctx_memory v)
      in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := rest, vctx_memory := new_memory |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition extcodecopy :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "extcodecopy v c = (case vctx_stack v of
    addr # dst_start # src_start # len # rest \<Rightarrow>
      let src_start64 = (if Word.uint src_start \<ge> 2^64 then 2^64 - 1 else Word.uint src_start);
          len64 = Word.uint len;
          data = cut_natural_map (nat src_start64) (nat len64) (program_as_natural_map (vctx_ext_program v (Word.ucast addr)))
      in let new_memory = store_byte_list_memory dst_start data (vctx_memory v)
      in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := rest, vctx_memory := new_memory |)))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition mcopy :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"mcopy v c = (case vctx_stack v of
  dst # src # len # rest \<Rightarrow>
    let data = cut_memory src len (vctx_memory v);
        new_memory = store_byte_list_memory dst data (vctx_memory v)
    in InstructionContinue (vctx_advance_pc c
         (v (| vctx_stack := rest, vctx_memory := new_memory |)))
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition returndatacopy :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"returndatacopy v c = (case vctx_stack v of
  dst_start # src_start # len # rest \<Rightarrow>
    if Word.uint src_start \<ge> 2^64 then
      instruction_failure_result v [ReturnDataOutOfBounds]
    else
      let src_end = src_start + len;
          return_data_length = word_of_int (length (vctx_returned_data v))
      in if Word.uint src_end \<ge> 2^64 \<or>
            src_end > return_data_length then
        instruction_failure_result v [ReturnDataOutOfBounds]
      else
        let data = cut_natural_map (unat src_start) (unat len) 
                    (input_as_natural_map (vctx_returned_data v));
            new_memory = store_byte_list_memory dst_start data (vctx_memory v)
        in InstructionContinue (vctx_advance_pc c 
             (v (| vctx_stack := rest, vctx_memory := new_memory |)))
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition pc :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "pc v c = InstructionContinue (vctx_advance_pc c (v (| vctx_stack := word_of_int (vctx_pc v) # vctx_stack v |)))"

definition create_log_entry :: "nat \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> log_entry" where
  "create_log_entry n v c = (| log_addr = cctx_this c,
                               log_topics = List.drop 2 (List.take (n + 2) (vctx_stack v)),
                               log_data = vctx_returned_bytes v |)"

definition log :: "nat \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "log n v c = (
    let new_log_entry = create_log_entry n v c;
        updated_v = v (| vctx_logs := new_log_entry # vctx_logs v |);
        advanced_v = vctx_advance_pc c (vctx_pop_stack (n + 2) updated_v)
    in InstructionContinue advanced_v)"

fun get_byte :: "256 word \<Rightarrow> 256 word \<Rightarrow> 256 word" where 
  "get_byte position w = (
    if Word.uint position \<ge> 32 then 0 else
    case index (word_rsplit w) (nat (abs (Word.uint position))) of
      None \<Rightarrow> 0 |
      Some (a::byte) \<Rightarrow> Word.ucast a
  )"

definition inst_shl :: "u256 \<Rightarrow> u256 \<Rightarrow> u256" where
"inst_shl in_shift in_value = (
  if in_shift < 256 then word_of_int (Word.uint in_value << (unat in_shift))
  else 0)"

definition inst_shr :: "u256 \<Rightarrow> u256 \<Rightarrow> u256" where
"inst_shr in_shift in_value = (
  if in_shift < 256 then word_of_int (Word.uint in_value >> (unat in_shift))
  else 0)"

definition inst_sar :: "u256 \<Rightarrow> u256 \<Rightarrow> u256" where
"inst_sar in_shift in_value = (
  if in_shift \<ge> 256 then
    if Word.uint in_value \<ge> 2^255 then -1 else 0
  else
    let n = unat in_shift in
    if Word.uint in_value \<ge> 2^255 then
      word_of_int ((Word.uint in_value >> n) + ((2^n - 1) << (256 - n)))
    else 
      word_of_int (Word.uint in_value >> n))"

(* The name is same as Keccak256 in the EVM *)
definition sha3 :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
  "sha3 v c = 
    (case vctx_stack v of
       start # len # rest =>
         let lst = cut_memory start len (vctx_memory v) in
         if \<not> cctx_hash_filter c lst then instruction_failure_result v [OutOfGas]
         else InstructionContinue (vctx_advance_pc c (v (| vctx_stack := keccak lst # rest |)))
     | _ => instruction_failure_result v [TooShortStack])"

definition signextend :: "u256 \<Rightarrow> u256 \<Rightarrow> u256" where
  "signextend len w = (
    if Word.uint len \<ge> 31 then
      w
    else
      let len_bits = 8 * (unat len + 1);
          mask = 2 ^ len_bits - 1;
          masked = and w mask
      in if word_sless masked (2 ^ (len_bits - 1)) then
           masked
         else
           masked - mask - 1
  )"

definition extcodehash :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"extcodehash v c = (case vctx_stack v of
  addr # rest \<Rightarrow> 
    let a = Word.ucast addr;
        p = vctx_ext_program v a;
        hash = (if \<not>(vctx_account_existence v a) then 0 
               else keccak (program_byte_content p))
    in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := hash # rest |)))
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition returndatasize :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"returndatasize v c = stack_0_1_op v c (word_of_int (length (vctx_returned_data v)))"

definition chainid :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"chainid v c = stack_0_1_op v c (vctx_chainid v)"

definition selfbalance :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where 
"selfbalance v c = stack_0_1_op v c (vctx_balance v (cctx_this c))"

definition basefee :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"basefee v c = stack_0_1_op v c (block_basefee (vctx_block v))"

definition blobhash :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"blobhash v c = (case vctx_stack v of
  idx # rest \<Rightarrow> 
    let hash = (if Word.uint idx < length (vctx_blobHashes v) \<and> (Word.uint idx < 2^64) then
                  nth (vctx_blobHashes v) (unat idx)
                else 0)
    in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := hash # rest |)))
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition blobbasefee :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"blobbasefee v c = stack_0_1_op v c (block_blobbasefee (vctx_block v))"

definition tload :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"tload v c = (case vctx_stack v of
  loc # rest \<Rightarrow> 
    let value = vctx_transient_storage v loc
    in InstructionContinue (vctx_advance_pc c (v (| vctx_stack := value # rest |)))
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition tstore :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"tstore v c = (case vctx_stack v of
  loc # val # rest \<Rightarrow>
    let new_v = v (| vctx_stack := rest,
                    vctx_transient_storage := (\<lambda>x. if x = loc then val else vctx_transient_storage v x) |)
    in InstructionContinue (vctx_advance_pc c new_v)
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition create2 :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"create2 v c = (case vctx_stack v of
  val # in_off # in_size # salt # rest \<Rightarrow>
    let code = cut_memory in_off in_size (vctx_memory v);
        keccak_code = keccak code
    in InstructionToEnvironment
         (ContractCreate2 (| create2arg_value = val, create2arg_salt = salt, create2arg_code_hash = keccak_code |))
         (v (| vctx_stack := rest |))
         (Some (0, 0))
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition staticcall :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
"staticcall v c net = (case vctx_stack v of
  temp # to # in_off # in_size # out_off # out_size # rest \<Rightarrow>
    (case calc_memu_extra (vctx_memory_usage v) temp 0 0 in_off in_size out_off out_size of
      CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
    | CalculationSuccess memu_extra \<Rightarrow>
        (case Ccallgas v temp to 0 (\<not> (vctx_account_existence v (Word.ucast to))) (vctx_gas v) net 
              (CalculationSuccess memu_extra) of
          CalcFailureReason reason \<Rightarrow> instruction_failure_result v [reason]
        | CalculationSuccess call_gas \<Rightarrow>
            InstructionToEnvironment
              (ContractStaticCall
                \<lparr> callarg_gas = word_of_int call_gas,
                  callarg_code = Word.ucast to,
                  callarg_recipient = Word.ucast to,
                  callarg_value = 0,
                  callarg_data = cut_memory in_off in_size (vctx_memory v),
                  callarg_output_begin = out_off,
                  callarg_output_size = out_size \<rparr>)
              (vctx_advance_pc c (v \<lparr> vctx_stack := rest \<rparr>))
              (Some (Word.uint out_off, Word.uint out_size))))
  | _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition revert :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"revert v c = (case vctx_stack v of
  in_off # in_size # _ \<Rightarrow>
    let data = cut_memory in_off in_size (vctx_memory v)
    in InstructionToEnvironment (ContractFail []) v (Some (Word.uint in_off, Word.uint in_size))
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"

definition invalid :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> instruction_result" where
"invalid v c = instruction_failure_result v [ShouldNotHappen]"

(* selfdestruct is empty in the AOT compiler *)
definition selfdestruct :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> instruction_result" where
"selfdestruct v c net = (case vctx_stack v of
  recipient # _ \<Rightarrow>
    let addr = Word.ucast recipient;
        empty = \<not>(vctx_account_existence v addr)
    in if vctx_gas v < Gselfdestruct net empty
       then instruction_failure_result v [OutOfGas]
       else InstructionToEnvironment (ContractSuicide addr) v None
| _ \<Rightarrow> instruction_failure_result v [TooShortStack])"


definition account_access_gas :: "variable_ctx \<Rightarrow> address \<Rightarrow> int" where
  "account_access_gas v addr = (if addr \<in> set (vctx_warm_addresses v) then WarmStorageReadCostEIP2929 else ColdAccountAccessCostEIP2929)"

definition add_warm_address :: "variable_ctx \<Rightarrow> address \<Rightarrow> variable_ctx" where
  "add_warm_address v addr = (if addr \<in> set (vctx_warm_addresses v) then v else v\<lparr>vctx_warm_addresses := addr # vctx_warm_addresses v\<rparr>)"

definition mark_account_access :: "variable_ctx \<Rightarrow> address \<Rightarrow> instruction_result \<Rightarrow> instruction_result" where
  "mark_account_access v addr r = (case r of
      InstructionContinue v' => InstructionContinue (add_warm_address v' addr)
    | _ => r)"

definition mark_call_account_access :: "variable_ctx \<Rightarrow> address \<Rightarrow> instruction_result \<Rightarrow> instruction_result" where
  "mark_call_account_access v addr r = (case r of
      InstructionToEnvironment (ContractFail _) _ _ => r
    | InstructionToEnvironment a v' e => InstructionToEnvironment a (add_warm_address v' addr) e
    | InstructionContinue v' => InstructionContinue (add_warm_address v' addr))"

definition thirdComponentOfC :: "inst \<Rightarrow> variable_ctx \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> bool \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> int \<Rightarrow> network \<Rightarrow> calculation_result \<Rightarrow> calculation_result" where
"thirdComponentOfC i v s0 s1 s2 s3 recipient_empty orig_val new_val remaining_gas net memu_extra = (
  case i of
    Stack (PUSH_N _) \<Rightarrow> CalculationSuccess Gfasteststep
  | Stack POP \<Rightarrow> CalculationSuccess Gquickstep  
  | Stack PUSH0 \<Rightarrow> if at_least_shanghai net then CalculationSuccess Gquickstep else CalculationSuccess 0
  | Stack CALLDATALOAD \<Rightarrow> CalculationSuccess Gfasteststep
  | Dup _ \<Rightarrow> CalculationSuccess Gfasteststep
  | Swap _ \<Rightarrow> CalculationSuccess Gfasteststep

  | Storage SSTORE \<Rightarrow> CalculationSuccess (sstore_gas net s0 (vctx_storage_at_call v s0) orig_val new_val v)
  | Storage SLOAD \<Rightarrow> CalculationSuccess (if s0 \<in> set (vctx_touched_storage_index v) then WarmStorageReadCostEIP2929 else ColdSloadCostEIP2929)

  | Memory MLOAD \<Rightarrow> handle_memory_expansion_gas v (Memory MLOAD) Gfasteststep
  | Memory MSTORE \<Rightarrow> handle_memory_expansion_gas v (Memory MSTORE) Gfasteststep
  | Memory MSTORE8 \<Rightarrow> handle_memory_expansion_gas v (Memory MSTORE8) Gfasteststep
  | Memory CALLDATACOPY \<Rightarrow> handle_memory_copy_gas v (Memory CALLDATACOPY) Gfasteststep 2 s2
  | Memory CODECOPY \<Rightarrow> handle_memory_copy_gas v (Memory CODECOPY) Gfasteststep 2 s2
  | Memory EXTCODECOPY \<Rightarrow> handle_memory_copy_gas v (Memory EXTCODECOPY) (account_access_gas v (Word.ucast s0)) 3 s3  \<comment> \<open> NOTE: EIP2929 cold account access \<close>
  | Memory MCOPY \<Rightarrow> if at_least_cancun net then handle_memory_copy_gas v (Memory MCOPY) Gfasteststep 2 s2 else CalculationSuccess 0
  | Memory RETURNDATACOPY \<Rightarrow> handle_memory_copy_gas v (Memory RETURNDATACOPY) Gfasteststep 2 s2
  | Memory MSIZE \<Rightarrow> CalculationSuccess Gquickstep
  | Memory TLOAD \<Rightarrow> if at_least_cancun net then CalculationSuccess Gtload else CalculationSuccess 0
  | Memory TSTORE \<Rightarrow> if at_least_cancun net then CalculationSuccess Gtstore else CalculationSuccess 0

  | Pc JUMPI \<Rightarrow> CalculationSuccess Gslowstep
  | Pc JUMP \<Rightarrow> CalculationSuccess Gmidstep
  | Pc JUMPDEST \<Rightarrow> CalculationSuccess Gjumpdest
  | Pc PC \<Rightarrow> CalculationSuccess Gquickstep

  | Arith ADD \<Rightarrow> CalculationSuccess Gfasteststep
  | Arith SUB \<Rightarrow> CalculationSuccess Gfasteststep
  | Arith ISZERO \<Rightarrow> CalculationSuccess Gfasteststep
  | Arith MUL \<Rightarrow> CalculationSuccess Gfaststep
  | Arith DIV \<Rightarrow> CalculationSuccess Gfaststep
  | Arith MOD \<Rightarrow> CalculationSuccess Gfaststep
  | Arith ADDMOD \<Rightarrow> CalculationSuccess Gmidstep
  | Arith MULMOD \<Rightarrow> CalculationSuccess Gmidstep
  | Arith EXP \<Rightarrow> (
      let exp_bytes = (bit_length s1 + 7) div 8;
          exp_byte_gas = Gexpbyte net * exp_bytes
      in if Gexp + exp_byte_gas \<ge> 2^64 then CalcFailureReason GasUintOverflow
         else CalculationSuccess (Gexp + exp_byte_gas))
  | Arith inst_GT \<Rightarrow> CalculationSuccess Gfasteststep
  | Arith inst_EQ \<Rightarrow> CalculationSuccess Gfasteststep  
  | Arith inst_LT \<Rightarrow> CalculationSuccess Gfasteststep
  | Arith KECCAK256 \<Rightarrow> handle_sha3_gas v (Arith KECCAK256) Gsha3 s1

  | Sarith SDIV \<Rightarrow> CalculationSuccess Gfaststep
  | Sarith SMOD \<Rightarrow> CalculationSuccess Gfaststep
  | Sarith SGT \<Rightarrow> CalculationSuccess Gfasteststep
  | Sarith SLT \<Rightarrow> CalculationSuccess Gfasteststep
  | Sarith SIGNEXTEND \<Rightarrow> CalculationSuccess Gfaststep

  | Bits inst_AND \<Rightarrow> CalculationSuccess Gfasteststep
  | Bits inst_OR \<Rightarrow> CalculationSuccess Gfasteststep
  | Bits inst_XOR \<Rightarrow> CalculationSuccess Gfasteststep
  | Bits inst_NOT \<Rightarrow> CalculationSuccess Gfasteststep
  | Bits BYTE \<Rightarrow> CalculationSuccess Gfasteststep
  | Bits inst_SHL \<Rightarrow> CalculationSuccess Gfasteststep
  | Bits inst_SHR \<Rightarrow> CalculationSuccess Gfasteststep
  | Bits inst_SAR \<Rightarrow> CalculationSuccess Gfasteststep

  | Info CALLDATASIZE \<Rightarrow> CalculationSuccess Gquickstep
  | Info CALLER \<Rightarrow> CalculationSuccess Gquickstep
  | Info ADDRESS \<Rightarrow> CalculationSuccess Gquickstep
  | Info BALANCE \<Rightarrow> CalculationSuccess (account_access_gas v (Word.ucast s0))
  | Info ORIGIN \<Rightarrow> CalculationSuccess Gquickstep
  | Info CALLVALUE \<Rightarrow> CalculationSuccess Gquickstep
  | Info CODESIZE \<Rightarrow> CalculationSuccess Gquickstep
  | Info GASPRICE \<Rightarrow> CalculationSuccess Gquickstep
  | Info EXTCODESIZE \<Rightarrow> CalculationSuccess (account_access_gas v (Word.ucast s0))
  | Info BLOCKHASH \<Rightarrow> CalculationSuccess Gextstep
  | Info COINBASE \<Rightarrow> CalculationSuccess Gquickstep
  | Info TIMESTAMP \<Rightarrow> CalculationSuccess Gquickstep
  | Info NUMBER \<Rightarrow> CalculationSuccess Gquickstep
  | Info DIFFICULTY \<Rightarrow> CalculationSuccess Gquickstep
  | Info GASLIMIT \<Rightarrow> CalculationSuccess Gquickstep
  | Info GAS \<Rightarrow> CalculationSuccess Gquickstep
  | Info EXTCODEHASH \<Rightarrow> CalculationSuccess (account_access_gas v (Word.ucast s0))
  | Info RETURNDATASIZE \<Rightarrow> CalculationSuccess Gquickstep
  | Info CHAINID \<Rightarrow> CalculationSuccess Gquickstep
  | Info SELFBALANCE \<Rightarrow> CalculationSuccess Gfaststep
  | Info BASEFEE \<Rightarrow> if at_least_london net then CalculationSuccess Gquickstep else CalculationSuccess 0
  | Info BLOBHASH \<Rightarrow> if at_least_cancun net then CalculationSuccess Gfasteststep else CalculationSuccess 0
  | Info BLOBBASEFEE \<Rightarrow> if at_least_cancun net then CalculationSuccess Gquickstep else CalculationSuccess 0

  | Log LOG0 \<Rightarrow> handle_log_gas v (Log LOG0) 0 s1
  | Log LOG1 \<Rightarrow> handle_log_gas v (Log LOG1) 1 s1
  | Log LOG2 \<Rightarrow> handle_log_gas v (Log LOG2) 2 s1
  | Log LOG3 \<Rightarrow> handle_log_gas v (Log LOG3) 3 s1
  | Log LOG4 \<Rightarrow> handle_log_gas v (Log LOG4) 4 s1

  | Misc CREATE \<Rightarrow> handle_create_gas v (Misc CREATE) Gcreate s2
  | Misc CREATE2 \<Rightarrow> handle_create2_gas v (Misc CREATE2) Gcreate2 s2
  | Misc CALL \<Rightarrow> Ccall v s0 s1 s2 recipient_empty remaining_gas net memu_extra
  | Misc CALLCODE \<Rightarrow> Ccall v s0 s1 s2 recipient_empty remaining_gas net memu_extra
  | Misc DELEGATECALL \<Rightarrow> Ccall v s0 s1 0 recipient_empty remaining_gas net memu_extra
  | Misc STATICCALL \<Rightarrow> Ccall v s0 s1 0 recipient_empty remaining_gas net memu_extra
  | Misc RETURN \<Rightarrow> handle_memory_expansion_gas v (Misc RETURN) Gzero
  | Misc REVERT \<Rightarrow> handle_memory_expansion_gas v (Misc REVERT) Gzero
  | Misc INVALID \<Rightarrow> CalculationSuccess Gzero
  | Misc SELFDESTRUCT \<Rightarrow> CalculationSuccess Gzero
  | Misc STOP \<Rightarrow> CalculationSuccess Gzero 

  | _ \<Rightarrow> CalculationSuccess 0)"

definition C :: "int \<Rightarrow> int \<Rightarrow> inst \<Rightarrow> variable_ctx \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> bool \<Rightarrow> u256 \<Rightarrow> u256 \<Rightarrow> int \<Rightarrow> network \<Rightarrow> calculation_result" where
"C old_memory_consumption new_memory_consumption1 i v s0 s1 s2 s3 recipient_empty orig new_val remaining_gas net = (
  let memu_extra = Cmem (max old_memory_consumption new_memory_consumption1) - Cmem old_memory_consumption
  in if memu_extra < 0 then CalcFailureReason GasUintOverflow
     else thirdComponentOfC i v s0 s1 s2 s3 recipient_empty orig new_val remaining_gas net (CalculationSuccess memu_extra))"

definition meter_gas :: "inst \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> calculation_result" where
"meter_gas i v c net = (
  let musage = (max(0)(vctx_memory_usage v));
      new_memory = new_memory_consumption i musage (vctx_stack_default 0 v) (vctx_stack_default 1 v)
                    (vctx_stack_default 2 v) (vctx_stack_default 3 v)
                    (vctx_stack_default 4 v) (vctx_stack_default 5 v)
                    (vctx_stack_default 6 v)
  in case new_memory of
       CalcFailureReason r \<Rightarrow> CalcFailureReason r
     | CalculationSuccess new_mem_size \<Rightarrow>
         C musage new_mem_size i v
           (vctx_stack_default 0 v) (vctx_stack_default 1 v) (vctx_stack_default 2 v) (vctx_stack_default 3 v)
           (\<not> ((vctx_account_existence v) (vctx_recipient v c))) ((vctx_storage v) (vctx_stack_default 0 v))
           (vctx_stack_default 1 v) (vctx_gas v) net)"

definition check_resources :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> (u256) list \<Rightarrow> inst \<Rightarrow> network \<Rightarrow> check_resources_result" where
"check_resources v c s i net = (
  let (consumed, produced) = inst_stack_numbers i;
      stack_ok = (int (List.length s) + produced - consumed) \<le> 1024;
      gas_check = meter_gas i v c net
  in if stack_ok then
       (case gas_check of
          CalculationSuccess gas_val \<Rightarrow> CheckSuccess (gas_val \<le> (vctx_gas v))
        | CalcFailureReason reason \<Rightarrow> CheckFailureReason reason)
     else CheckFailureReason TooLongStack
  )"

fun subtract_gas :: "int \<Rightarrow> int \<Rightarrow> instruction_result \<Rightarrow> instruction_result" where
  "subtract_gas gas_used new_memory_usage result = (
    let update_ctx = (\<lambda>v. v \<lparr> 
      vctx_gas := vctx_gas v - gas_used,
      vctx_memory_usage := new_memory_usage 
    \<rparr>)
    in case result of
      InstructionContinue v \<Rightarrow> 
        InstructionContinue (update_ctx v)
    | InstructionToEnvironment action v option \<Rightarrow>
        InstructionToEnvironment action (update_ctx v) option
  )"

fun bind_calc :: "calculation_result \<Rightarrow> variable_ctx \<Rightarrow> (int \<Rightarrow> instruction_result) \<Rightarrow> instruction_result" where
  "bind_calc (CalcFailureReason reason) v _ = instruction_failure_result v [reason]"
| "bind_calc (CalculationSuccess value_re) _ cont_fun = cont_fun value_re"

definition instruction_sem :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> inst \<Rightarrow> network \<Rightarrow> instruction_result" where
"instruction_sem v c inst net =
  bind_calc (new_memory_consumption inst (vctx_memory_usage v)
                (vctx_stack_default 0 v) (vctx_stack_default 1 v)
                (vctx_stack_default 2 v) (vctx_stack_default 3 v)
                (vctx_stack_default 4 v) (vctx_stack_default 5 v)
                (vctx_stack_default 6 v)) v
    (\<lambda>new_mem_size.
      bind_calc (meter_gas inst v c net) v
        (\<lambda>gas_consumption.
          if gas_consumption \<le> vctx_gas v then
            subtract_gas gas_consumption (toWordSize (max (vctx_memory_usage v) new_mem_size) * 32)
              (case inst of
                Stack (PUSH_N lst) => stack_0_1_op v c (Word.word_rcat (constant_mark lst))
              | Stack POP => pop v c
              | Stack PUSH0 => if at_least_shanghai net then push0 v c else instruction_failure_result v [ShouldNotHappen]
              | Stack CALLDATALOAD => stack_1_1_op v c (cut_data v)
              | Dup n => general_dup n v c
              | Swap n => swap (unat n) v c

              | Storage SSTORE => sstore net v c
              | Storage SLOAD => sload v c

              | Memory MLOAD => mload v c
              | Memory MSTORE => mstore v c
              | Memory MSTORE8 => mstore8 v c
              | Memory CALLDATACOPY => calldatacopy v c
              | Memory CODECOPY => codecopy v c
              | Memory EXTCODECOPY => mark_account_access v (Word.ucast (vctx_stack_default 0 v)) (extcodecopy v c)
              | Memory MCOPY => if at_least_cancun net then mcopy v c else instruction_failure_result v [ShouldNotHappen]
              | Memory RETURNDATACOPY => returndatacopy v c
              | Memory MSIZE => stack_0_1_op v c (word_of_int (vctx_memory_usage v))
              | Memory TLOAD => if at_least_cancun net then tload v c else instruction_failure_result v [ShouldNotHappen]
              | Memory TSTORE => if at_least_cancun net then tstore v c else instruction_failure_result v [ShouldNotHappen]

              | Pc JUMP => jump v c
              | Pc JUMPI => jumpi v c
              | Pc JUMPDEST => stack_0_0_op v c
              | Pc PC => pc v c

              | Arith ADD => stack_2_1_op v c (\<lambda>a b. a + b)
              | Arith SUB => stack_2_1_op v c (\<lambda>a b. a - b)
              | Arith ISZERO => stack_1_1_op v c (\<lambda>a. if a = 0 then 1 else 0)
              | Arith MUL => stack_2_1_op v c (\<lambda>a b. a * b)
              | Arith DIV => stack_2_1_op v c (\<lambda>a divisor. if divisor = 0 then 0 else word_of_int (Word.uint a div Word.uint divisor))
              | Arith MOD => stack_2_1_op v c (\<lambda>a divisor. if divisor = 0 then 0 else word_of_int (Word.uint a mod Word.uint divisor))
              | Arith ADDMOD => stack_3_1_op v c (\<lambda>a b divisor. if divisor = 0 then 0 else word_of_int ((Word.uint a + Word.uint b) mod Word.uint divisor))
              | Arith MULMOD => stack_3_1_op v c (\<lambda>a b divisor. if divisor = 0 then 0 else word_of_int ((Word.uint a * Word.uint b) mod Word.uint divisor))
              | Arith EXP => stack_2_1_op v c (\<lambda>a exponent. word_of_int (word_exp (Word.uint a) (unat exponent)))
              | Arith inst_GT => stack_2_1_op v c (\<lambda>a b. if a > b then 1 else 0)
              | Arith inst_EQ => stack_2_1_op v c (\<lambda>a b. if a = b then 1 else 0)
              | Arith inst_LT => stack_2_1_op v c (\<lambda>arg0 arg1. if arg1 > arg0 then 1 else 0)
              | Arith KECCAK256 => sha3 v c

              | Sarith SDIV => stack_2_1_op v c (\<lambda>n divisor. if divisor = 0 then 0 else
                  let divisor = sintFromW256 divisor;
                      n = sintFromW256 n;
                      min_int = - (2 ^ 255)
                  in if n = min_int \<and> divisor = -1 then word_of_int min_int
                    else if divisor < 0 then
                      if n < 0 then word_of_int ((-1 * n) div (-1 * divisor))
                      else word_of_int (-1 * (n div (-1 * divisor)))
                    else if n < 0 then word_of_int (-1 * ((-1 * n) div divisor))
                    else word_of_int (n div divisor))
              | Sarith SMOD => stack_2_1_op v c (\<lambda>n divisor. if divisor = 0 then 0 else
                  let divisor = sintFromW256 divisor;
                      n = sintFromW256 n
                  in if divisor < 0 then
                      if n < 0 then word_of_int (-1 * ((-1 * n) mod (-1 * divisor)))
                      else word_of_int (n mod (-1 * divisor))
                    else if n < 0 then word_of_int (-1 * ((-1 * n) mod divisor))
                    else word_of_int (n mod divisor))
              | Sarith SGT => stack_2_1_op v c (\<lambda>elm0 elm1. if word_sless elm1 elm0 then 1 else 0)
              | Sarith SLT => stack_2_1_op v c (\<lambda>elm0 elm1. if word_sless elm0 elm1 then 1 else 0)
              | Sarith SIGNEXTEND => stack_2_1_op v c signextend

              | Bits inst_AND => stack_2_1_op v c (\<lambda>a b. and a b)
              | Bits inst_OR => stack_2_1_op v c (\<lambda>a b. or a b)
              | Bits inst_XOR => stack_2_1_op v c (\<lambda>a b. xor a b)
              | Bits inst_NOT => stack_1_1_op v c (\<lambda>a. not a)
              | Bits BYTE => stack_2_1_op v c get_byte
              | Bits inst_SHL => stack_2_1_op v c inst_shl
              | Bits inst_SHR => stack_2_1_op v c inst_shr
              | Bits inst_SAR => stack_2_1_op v c inst_sar

              | Info CALLDATASIZE => stack_0_1_op v c (datasize v)
              | Info CALLER => stack_0_1_op v c (Word.ucast (vctx_caller v))
              | Info ADDRESS => stack_0_1_op v c (Word.ucast (cctx_this c))
              | Info BALANCE => mark_account_access v (Word.ucast (vctx_stack_default 0 v)) (stack_1_1_op v c (\<lambda>a. vctx_balance v (Word.ucast a)))
              | Info ORIGIN => stack_0_1_op v c (Word.ucast (vctx_origin v))
              | Info CALLVALUE => stack_0_1_op v c (vctx_value_sent v)
              | Info CODESIZE => stack_0_1_op v c (word_of_int (int (length (program_byte_content (cctx_program c)))))
              | Info GASPRICE => stack_0_1_op v c (vctx_gasprice v)
              | Info EXTCODESIZE => mark_account_access v (Word.ucast (vctx_stack_default 0 v)) (stack_1_1_op v c (\<lambda>arg1. word_of_int (int (length (program_byte_content (vctx_ext_program v (Word.ucast arg1)))))))
              | Info BLOCKHASH => stack_1_1_op v c (block_blockhash (vctx_block v))
              | Info COINBASE => stack_0_1_op v c (Word.ucast (block_coinbase (vctx_block v)))
              | Info TIMESTAMP => stack_0_1_op v c (block_timestamp (vctx_block v))
              | Info NUMBER => stack_0_1_op v c (block_number (vctx_block v))
              | Info DIFFICULTY => if at_least_paris net then stack_0_1_op v c (block_prevrandao (vctx_block v)) else stack_0_1_op v c (block_difficulty (vctx_block v))
              | Info GASLIMIT => stack_0_1_op v c (block_gaslimit (vctx_block v))
              | Info GAS => stack_0_1_op v c (gas v - 2)
              | Info EXTCODEHASH => mark_account_access v (Word.ucast (vctx_stack_default 0 v)) (extcodehash v c)
              | Info RETURNDATASIZE => returndatasize v c
              | Info CHAINID => chainid v c
              | Info SELFBALANCE => selfbalance v c
              | Info BASEFEE => if at_least_london net then basefee v c else instruction_failure_result v [ShouldNotHappen]
              | Info BLOBHASH => if at_least_cancun net then blobhash v c else instruction_failure_result v [ShouldNotHappen]
              | Info BLOBBASEFEE => if at_least_cancun net then blobbasefee v c else instruction_failure_result v [ShouldNotHappen]

              | Log LOG0 => log 0 v c
              | Log LOG1 => log 1 v c
              | Log LOG2 => log 2 v c
              | Log LOG3 => log 3 v c
              | Log LOG4 => log 4 v c

              | Misc CREATE => create v c
              | Misc CREATE2 => if at_least_cancun net then create2 v c else instruction_failure_result v [ShouldNotHappen]
              | Misc CALL => mark_call_account_access v (Word.ucast (vctx_stack_default 1 v)) (call net v c)
              | Misc CALLCODE => mark_call_account_access v (Word.ucast (vctx_stack_default 1 v)) (callcode net v c)
              | Misc DELEGATECALL => if before_homestead net then instruction_failure_result v [ShouldNotHappen] else mark_call_account_access v (Word.ucast (vctx_stack_default 1 v)) (delegatecall net v c)
              | Misc STATICCALL => if at_least_cancun net then mark_call_account_access v (Word.ucast (vctx_stack_default 1 v)) (staticcall v c net) else instruction_failure_result v [ShouldNotHappen]
              | Misc RETURN => ret v c
              | Misc REVERT => revert v c
              | Misc INVALID => invalid v c
              | Misc SELFDESTRUCT => selfdestruct v c net
              | Misc STOP => stop v c

              | Unknown _ => instruction_failure_result v [InvalidOpcode])
          else instruction_failure_result v [OutOfGas]
        )
     )"

fun program_sem :: "constant_ctx \<Rightarrow> nat \<Rightarrow> network \<Rightarrow> instruction_result \<Rightarrow> instruction_result" where
  "program_sem c 0 net pr1 = pr1" |
  "program_sem c (Suc fuel_pred) net pr1 = (
    case pr1 of
      InstructionToEnvironment _ _ _ \<Rightarrow> pr1 |
      InstructionContinue v \<Rightarrow>
      (case vctx_next_instruction v c of
        None \<Rightarrow> InstructionToEnvironment (ContractReturn []) v None |
        Some i \<Rightarrow>
        (case check_resources v c (vctx_stack v) i net of   \<comment> \<open>we need check before? or only need check stack? \<close>
          CheckSuccess ok \<Rightarrow> 
            if ok then
              if vctx_gas v \<le> 0 then
                instruction_sem v c i net
              else
                program_sem c fuel_pred net (instruction_sem v c i net)
            else
              instruction_failure_result v [OutOfGas]
        | CheckFailureReason reason \<Rightarrow>
            instruction_failure_result v [reason])))"

(* Execute EVM bytecode *)
definition execute_evm_bytecode :: "char list \<Rightarrow> variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> network \<Rightarrow> nat \<Rightarrow> instruction_result" where
  "execute_evm_bytecode bytecode v c net fuel = (
    let insts = parse_bytecode bytecode;
        program = program_of_lst insts program_content_of_lst;
        program = program\<lparr>program_byte_content := bytes_of_hex_content bytecode\<rparr>;
        c = c\<lparr>cctx_program := program\<rparr>;
        initial_result = InstructionContinue (if fuel > 0 then v\<lparr>vctx_gas := fuel\<rparr> else v)
    in program_sem c (nat (vctx_gas v)) net initial_result
  )"

end
