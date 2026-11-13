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

fun at_least_berlin :: "network \<Rightarrow> bool" where
  "at_least_berlin Berlin = True" |
  "at_least_berlin London = True" |
  "at_least_berlin Paris = True" |
  "at_least_berlin Shanghai = True" |
  "at_least_berlin Cancun = True" |
  "at_least_berlin _ = False"

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

fun at_least_paris :: "network \<Rightarrow> bool" where
  "at_least_paris Paris = True" |
  "at_least_paris Shanghai = True" |
  "at_least_paris Cancun = True" |
  "at_least_paris _ = False"

end
