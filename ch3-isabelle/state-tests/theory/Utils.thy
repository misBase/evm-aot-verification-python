theory Utils
  imports
    Main EVMCommType
begin

definition toWordSize :: "int \<Rightarrow> int" where
"toWordSize size_v = (
  if size_v > (2^64 - 31) then
    2^64 div 32 + 1
  else 
    (size_v + 31) div 32
)"

(* Helper function to find the most significant bit position *)
fun find_msb :: "256 word \<Rightarrow> nat \<Rightarrow> nat" where
"find_msb w i = (
  if i = 0 then 
    (if bit w 0 then 0 else 0)
  else if bit w i then 
    i
  else 
    find_msb w (i - 1)
)"

(* returns the number of bits in the binary representation of a number *)
definition bit_length :: "256 word \<Rightarrow> int" where
"bit_length w = (
  if w = 0 then 0
  else int (find_msb w 255 + 1)
)"

(* Test cases for bit_length *)
lemma bit_length_zero: "bit_length 0 = 0"
  by (simp add: bit_length_def)

lemma bit_length_two: "bit_length 2 = 2"
  by (simp add: bit_length_def find_msb.simps)

lemma bit_length_three: "bit_length 3 = 2"
  by (simp add: bit_length_def find_msb.simps)

(* Examples that can be computed *)
lemma "bit_length 0 = 0" by eval
lemma "bit_length 1 = 1" by eval
lemma "bit_length 2 = 2" by eval
lemma "bit_length 3 = 2" by eval
lemma "bit_length 4 = 3" by eval
lemma "bit_length 7 = 3" by eval
lemma "bit_length 8 = 4" by eval
lemma "bit_length 15 = 4" by eval
lemma "bit_length 16 = 5" by eval
lemma "bit_length 12010313013 = 34" by eval
lemma "bit_length 9223372036854775807 = 63" by eval

(* Basic utility functions *)
definition sintFromW256 :: "256 word \<Rightarrow> int" where 
  "sintFromW256 = sint"

fun word_exp :: "int \<Rightarrow> nat \<Rightarrow> int" where 
  "word_exp i 0 = 1" |
  "word_exp i n = (
    let half = n div 2;
        modulo = n mod 2;
        recur = word_exp i half
    in ((i ^ modulo) * recur * recur) mod (2 ^ 256)
  )"

fun log256floor :: "int \<Rightarrow> int" where 
  "log256floor x = (
    if x \<le> 255 then 0 
    else 1 + log256floor (x div 256)
  )"

fun index :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "index [] n = None" |
  "index (x # xs) 0 = Some x" |
  "index (x # xs) (Suc n) = index xs n"

definition word256FromNat :: "nat \<Rightarrow> u256" where 
  "word256FromNat i = word_of_int (int i)"

fun iota0 :: "u256 \<Rightarrow> nat \<Rightarrow> u256 list \<Rightarrow> u256 list" where 
  "iota0 start 0 rev_acc = List.rev rev_acc" |
  "iota0 start (Suc x) rev_acc = iota0 (start + 1) x (start # rev_acc)"

fun cut_memory_aux_alt :: "u256 \<Rightarrow> nat \<Rightarrow> (u256 \<Rightarrow> u8) \<Rightarrow> u8 list" where
  "cut_memory_aux_alt idx 0 memory = []" |
  "cut_memory_aux_alt idx (Suc n) memory = memory idx # cut_memory_aux_alt (idx + 1) n memory"

definition cut_memory :: "u256 \<Rightarrow> u256 \<Rightarrow> (w256 \<Rightarrow> byte) \<Rightarrow> byte list" where 
  "cut_memory idx n memory = cut_memory_aux_alt idx (unat n) memory"

end