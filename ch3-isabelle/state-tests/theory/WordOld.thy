theory WordOld
  imports
    Main
    EVMCommType EVM_state EVM_syntax
    "HOL.Bit_Operations"
begin

definition Bit :: "int \<Rightarrow> bool \<Rightarrow> int" (infixl "BIT" 90)
where
  "k BIT b = (if b then 1 else 0) + k + k"

definition bin_rest :: "int \<Rightarrow> int"
where
  "bin_rest w = w div 2"

definition bin_last :: "int \<Rightarrow> bool"
where
  "bin_last w \<longleftrightarrow> w mod 2 = 1"

primrec bin_split :: "nat \<Rightarrow> int \<Rightarrow> int \<times> int" where
  Z: "bin_split 0 w = (w, 0)"
  | Suc: "bin_split (Suc n) w = (let (w1, w2) = bin_split n (bin_rest w)
        in (w1, w2 BIT bin_last w))"

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
where
  "bin_rsplit_aux n m c bs =
    (if m = 0 | n = 0 then bs else
      let (a, b) = bin_split n c 
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
where
  "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

definition word_rsplit :: "'a :: len word => 'b :: len word list"
where
  "word_rsplit w = 
  map word_of_int (bin_rsplit (len_of TYPE ('b)) (len_of TYPE ('a),uint w))"

end