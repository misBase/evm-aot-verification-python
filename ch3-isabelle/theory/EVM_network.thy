theory EVM_network
  imports EVM_types
begin


(* Network version definitions *)
datatype network =
  Frontier | Homestead | EIP150 | EIP158 | Metropolis | Byzantium | Constantinople | 
  Petersburg | Istanbul | Berlin | London | Paris | Shanghai | Cancun

(* Network version check functions *)
fun at_least_eip150 :: "network \<Rightarrow> bool" where 
  "at_least_eip150 Frontier = False" |
  "at_least_eip150 Homestead = False" |
  "at_least_eip150 _ = True"

fun before_homestead :: "network \<Rightarrow> bool" where 
  "before_homestead Frontier = True" |
  "before_homestead _ = False"

fun at_least_cancun :: "network \<Rightarrow> bool" where
  "at_least_cancun Cancun = True" |
  "at_least_cancun _ = False"

fun at_least_shanghai :: "network \<Rightarrow> bool" where
  "at_least_shanghai Shanghai = True" |
  "at_least_shanghai Cancun = True" |
  "at_least_shanghai _ = False"

fun at_least_london :: "network \<Rightarrow> bool" where
  "at_least_london London = True" |
  "at_least_london Paris = True" |
  "at_least_london Shanghai = True" |
  "at_least_london Cancun = True" |
  "at_least_london _ = False"

end
