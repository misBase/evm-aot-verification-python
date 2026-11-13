theory EVM_context
  imports Main EVM_types
begin


record program =
  program_content :: "int \<Rightarrow> inst option"
  program_length :: "int"
  program_byte_content :: "byte list"

definition empty_program :: "program" where
  "empty_program = (|
    program_content = (\<lambda>x. None),
    program_length = 0,
    program_byte_content = []
  |)"

definition program_of_lst :: "(inst)list \<Rightarrow> ((inst)list \<Rightarrow> int \<Rightarrow> (inst)option) \<Rightarrow> program" where
  "program_of_lst lst program_content_formatter = (|
    program_content = program_content_formatter lst,
    program_length = int (List.length lst),
    program_byte_content = []
  |)"

definition program_as_natural_map :: "program \<Rightarrow> nat \<Rightarrow> u8" where
  "program_as_natural_map p idx = (
    (case (program_content p) (int idx) of
      None => 0
    | Some inst =>
        (case index (inst_code inst) 0 of
          None => 0
        | Some a => a
        )
    ))"

definition program_as_u8_list  :: \<open> program \<Rightarrow> u8 list \<close>  where 
 \<open> program_as_u8_list p = List.map (program_as_natural_map p) (genlist (\<lambda>i. i) (nat (program_length p)))\<close>


record variable_ctx = 
  vctx_stack :: "uint256 list" 
  vctx_memory :: "memory" 
  vctx_memory_usage :: "int" 
  vctx_storage :: "storage" 
  vctx_pc :: "int" 
  vctx_balance :: "address \<Rightarrow> uint256" 
  vctx_caller :: "address" 
  vctx_value_sent :: "uint256" 
  vctx_data_sent :: "byte list" 
  vctx_storage_at_call :: "storage" 
  vctx_balance_at_call :: "address \<Rightarrow> uint256" 
  vctx_origin :: "address" 
  vctx_ext_program :: "address \<Rightarrow> program" 
  vctx_block :: "block_info" 
  vctx_gas :: "int" 
  vctx_account_existence :: "address \<Rightarrow> bool" 
  vctx_touched_storage_index :: "uint256 list"
  vctx_warm_addresses :: "address list"
  vctx_logs :: "log_entry list" 
  vctx_refund :: "int" 
  vctx_gasprice :: "uint256" 
  vctx_returned_data :: "byte list"
  vctx_chainid :: "uint256"
  vctx_blobHashes :: "uint256 list"
  vctx_transient_storage :: "storage"
  vctx_readonly :: "bool"
  

record constant_ctx = 
  cctx_program :: "program" 
  cctx_this :: "address" 
  cctx_hash_filter :: "byte list \<Rightarrow> bool" 

definition vctx_stack_default :: "int \<Rightarrow> variable_ctx \<Rightarrow> uint256" where
  "vctx_stack_default idx v = (case index (vctx_stack v) (nat (abs idx)) of
    Some w \<Rightarrow> w                       
  | None \<Rightarrow> uint256_zero)"

definition update_balance :: "160 word \<Rightarrow> (uint256 \<Rightarrow> uint256) \<Rightarrow> (160 word \<Rightarrow> uint256) \<Rightarrow> 160 word \<Rightarrow> uint256" where
  "update_balance a f orig x = (if x = a then f (orig a) else orig x)"

definition vctx_pop_stack :: "nat \<Rightarrow> variable_ctx \<Rightarrow> variable_ctx" where
  "vctx_pop_stack n v = v (| vctx_stack := List.drop n (vctx_stack v) |)"

definition vctx_update_storage :: "uint256 \<Rightarrow> uint256 \<Rightarrow> variable_ctx \<Rightarrow> variable_ctx" where
  "vctx_update_storage idx val v = v (| vctx_storage := (\<lambda>x. if x = idx then val else vctx_storage v x) |)"

definition vctx_next_instruction :: "variable_ctx \<Rightarrow> constant_ctx \<Rightarrow> inst option" where
  "vctx_next_instruction v c = ((program_content (cctx_program c)) (vctx_pc v))"

definition vctx_advance_pc :: "constant_ctx \<Rightarrow> variable_ctx \<Rightarrow> variable_ctx" where
  "vctx_advance_pc c v = v (| vctx_pc := (case vctx_next_instruction v c of
    None \<Rightarrow> vctx_pc v + 1
  | Some inst \<Rightarrow> vctx_pc v + inst_size inst) |)"

end
