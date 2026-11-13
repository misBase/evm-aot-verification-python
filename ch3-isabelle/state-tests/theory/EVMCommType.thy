theory EVMCommType
imports
  Main
  "HOL-Library.Word"
begin

type_synonym u4 = "4 word"
type_synonym u8 = "8 word"
type_synonym i8 = "8 word"
type_synonym i16 = "16 word"
type_synonym u16 = "16 word"
type_synonym i32 = "32 word"
type_synonym u32 = "32 word"
type_synonym i64 = "64 word"
type_synonym u64 = "64 word"


type_synonym i128 = "128 word"
type_synonym u128 = "128 word"

type_synonym u256 = "256 word"
type_synonym byte = "8 word"

(* Basic type definitions *)
type_synonym w256 = u256
type_synonym address = "160 word"

fun index :: " 'a list \<Rightarrow> nat \<Rightarrow> 'a option "  where
   "index [] n = None"
 | "index (x # xs) 0 = Some x"
 | "index (x # xs) (Suc n) = index xs n"

context semiring_bit_operations
begin
definition shiftl :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl "<<" 55)
  where [code_unfold]: \<open>a << n = push_bit n a\<close>

lemma bit_shiftl_iff [bit_simps]:
  \<open>bit (a << m) n \<longleftrightarrow> m \<le> n \<and> possible_bit TYPE('a) n \<and> bit a (n - m)\<close>
  by (simp add: shiftl_def bit_simps)

definition shiftr :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl ">>" 55)
  where [code_unfold]: \<open>a >> n = drop_bit n a\<close>

lemma bit_shiftr_eq [bit_simps]:
  \<open>bit (a >> n) = bit a \<circ> (+) n\<close>
  by (simp add: shiftr_def bit_simps)

end

definition sshiftr :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>  (infixl \<open>>>>\<close> 55)
  where [code_unfold]: \<open>w >>> n = signed_drop_bit n w\<close>

notation or (infixr "OR" 59)
notation xor (infixr "XOR" 59)
notation "and" (infixr "AND" 59)
notation "not" ("NOT _" [58] 58)

definition genlist where
  "genlist f n = map f (upt 0 n)"

definition word64FromNat  :: \<open> nat \<Rightarrow> 64 word \<close>  where 
     \<open> word64FromNat i = ( ((\<lambda> i .  word_of_int ( i))) (int i))\<close> 
  for  "i"  :: " nat "

primrec bl_to_bin_aux :: "bool list \<Rightarrow> int \<Rightarrow> int"
  where
    Nil: "bl_to_bin_aux [] w = w"
  | Cons: "bl_to_bin_aux (b # bs) w = bl_to_bin_aux bs (of_bool b + 2 * w)"

definition bl_to_bin :: "bool list \<Rightarrow> int"
  where "bl_to_bin bs = bl_to_bin_aux bs 0"

primrec bin_to_bl_aux :: "nat \<Rightarrow> int \<Rightarrow> bool list \<Rightarrow> bool list"
  where
    Z: "bin_to_bl_aux 0 w bl = bl"
  | Suc: "bin_to_bl_aux (Suc n) w bl = bin_to_bl_aux n (w div 2) (odd w # bl)"

definition bin_to_bl :: "nat \<Rightarrow> int \<Rightarrow> bool list"
  where "bin_to_bl n w = bin_to_bl_aux n w []"

lemma size_bin_to_bl_aux: "length (bin_to_bl_aux n w bs) = n + length bs"
  by (induct n arbitrary: w bs) auto

lemma size_bin_to_bl [simp]: "length (bin_to_bl n w) = n"
  by (simp add: bin_to_bl_def size_bin_to_bl_aux)

lemma bl_bin_bl': "bin_to_bl (n + length bs) (bl_to_bin_aux bs w) = bin_to_bl_aux n w bs"
  apply (induct bs arbitrary: w n)
   apply auto
    apply (simp_all only: add_Suc [symmetric])
    apply (auto simp add: bin_to_bl_def)
  done

lemma bl_bin_bl [simp]: "bin_to_bl (length bs) (bl_to_bin bs) = bs"
  unfolding bl_to_bin_def
  apply (rule box_equals)
    apply (rule bl_bin_bl')
   prefer 2
   apply (rule bin_to_bl_aux.Z)
  apply simp
  done

lemma bl_to_bin_inj: "bl_to_bin bs = bl_to_bin cs \<Longrightarrow> length bs = length cs \<Longrightarrow> bs = cs"
  apply (rule_tac box_equals)
    defer
    apply (rule bl_bin_bl)
   apply (rule bl_bin_bl)
  apply simp
  done

subsection \<open>Semantic interpretation of \<^typ>\<open>bool list\<close> as \<^typ>\<open>int\<close>\<close>

lemma bin_bl_bin': "bl_to_bin (bin_to_bl_aux n w bs) = bl_to_bin_aux bs (take_bit n w)"
  by (induct n arbitrary: w bs) (auto simp: bl_to_bin_def take_bit_Suc ac_simps mod_2_eq_odd)

lemma bin_bl_bin [simp]: "bl_to_bin (bin_to_bl n w) = take_bit n w"
  by (auto simp: bin_to_bl_def bin_bl_bin')

lift_definition of_bl :: \<open>bool list \<Rightarrow> 'a::len word\<close>
  is bl_to_bin .

lift_definition to_bl :: \<open>'a::len word \<Rightarrow> bool list\<close>
  is \<open>bin_to_bl LENGTH('a)\<close>
  by (simp add: bl_to_bin_inj)

end