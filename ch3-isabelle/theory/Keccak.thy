theory Keccak
  imports
    Main EVMCommType
    WordOld
begin

definition rotl64 :: "u64 \<Rightarrow> nat \<Rightarrow> u64" where
  "rotl64 w n = ((w >> (64 - n)) OR (w << n))"

definition big :: "u64" where
  "big = (1 << 63)"

definition two31 :: "u64" where
  "two31 = (1 << 31)"

definition two15 :: "u64" where
  "two15 = (1 << 15)"

definition keccakf_randc :: "u64 list" where
  "keccakf_randc = [
    0x0000000000000001,
    0x0000000000000082 OR two15,
    0x000000000000008a OR big OR two15,
    0x0000000000000000 OR big OR two31 OR two15,
    0x000000000000008b OR two15,
    0x0000000000000001 OR two31,
    0x0000000000000081 OR big OR two31 OR two15,
    0x0000000000000009 OR big OR two15,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000000000009 OR two31 OR two15,
    0x000000000000000a OR two31,
    0x000000000000008b OR two31 OR two15,
    0x000000000000008b OR big,
    0x0000000000000089 OR big OR two15,
    0x0000000000000003 OR big OR two15,
    0x0000000000000002 OR big OR two15,
    0x0000000000000080 OR big,
    0x000000000000000a OR two15,
    0x000000000000000a OR big OR two31,
    0x0000000000000081 OR big OR two31 OR two15,
    0x0000000000000080 OR big OR two15,
    0x0000000000000001 OR two31,
    0x0000000000000008 OR big OR two31 OR two15
  ]"

definition keccakf_rotc :: "nat list" where
  "keccakf_rotc = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44
  ]"

definition keccakf_piln :: "nat list" where
  "keccakf_piln = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1
  ]"

definition get :: "u64 list \<Rightarrow> nat \<Rightarrow> u64" where
  "get lst n = (case index lst n of
    Some x => x
  | None => 0)"

definition get_n :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "get_n lst n = (case index lst n of
    Some x => x
  | None => 0)"

definition setf :: "u64 list \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 list" where
  "setf lst n w = (
    if List.length lst < n then                
      lst @ genlist (\<lambda>x. 0) (List.length lst - n - 1) @ [w]
    else
      List.take n lst @ [w] @ List.drop (n + 1) lst
  )"

definition theta1 :: "nat \<Rightarrow> u64 list \<Rightarrow> u64" where
  "theta1 i st = (
    get st i XOR
    get st (i + 5) XOR
    get st (i + 10) XOR
    get st (i + 15) XOR
    get st (i + 20)
  )"

definition theta_t :: "nat \<Rightarrow> u64 list \<Rightarrow> u64" where
  "theta_t i bc = (
    get bc ((i + 4) mod 5) XOR
    rotl64 (get bc ((i + 1) mod 5)) 1
  )"

definition theta :: "u64 list \<Rightarrow> u64 list" where
  "theta st = (
    let bc = genlist (\<lambda>i. theta1 i st) 5 in
    let t = genlist (\<lambda>i. theta_t i bc) 5 in
    genlist (\<lambda>ji. get st ji XOR get t (ji mod 5)) 25
  )"

definition rho_pi_inner :: "u64 * u64 list \<Rightarrow> nat \<Rightarrow> u64 * u64 list" where
  "rho_pi_inner t_st i = (
    let j = get_n keccakf_piln i in
    let bc = get (snd t_st) j in
    (bc, setf (snd t_st) j (rotl64 (fst t_st) (get_n keccakf_rotc i)))
  )"

definition rho_pi_changes :: "nat \<Rightarrow> u64 * u64 list \<Rightarrow> u64 * u64 list" where
  "rho_pi_changes i t_st = List.foldl rho_pi_inner t_st (genlist (\<lambda>x. x) i)"

definition rho_pi :: "u64 list \<Rightarrow> u64 list" where
  "rho_pi st = snd (rho_pi_changes 24 (get st 1, st))"

definition chi_for_j :: "u64 list \<Rightarrow> u64 list" where
  "chi_for_j st_slice = genlist (\<lambda>i. 
    (get st_slice i) XOR 
    ((NOT (get st_slice ((i + 1) mod 5))) AND 
    (get st_slice ((i + 2) mod 5)))
  ) 5"

definition filterI :: "'a list \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a list" where
  "filterI lst pred = List.map fst (List.filter (\<lambda>p. pred (snd p)) (List.zip lst (genlist (\<lambda>i. i) (List.length lst))))"

definition chi :: "u64 list \<Rightarrow> u64 list" where
  "chi st = List.concat (genlist (\<lambda>j. chi_for_j (filterI st (\<lambda>i. j * 5 \<le> i \<and> i \<le> j * 5 + 5))) 5)"

definition iota :: "nat \<Rightarrow> u64 list \<Rightarrow> u64 list" where
  "iota r st = setf st 0 (get st 0 XOR get keccakf_randc r)"

definition for_inner :: "u64 list \<Rightarrow> nat \<Rightarrow> u64 list" where
  "for_inner st r = iota r (chi (rho_pi (theta st)))"

definition keccakf_rounds :: "nat" where
  "keccakf_rounds = 24"

fun word_rsplit_aux :: "bool list \<Rightarrow> nat \<Rightarrow> u8 list" where
  "word_rsplit_aux lst 0 = []"
| "word_rsplit_aux lst (Suc n) = of_bl (List.take 8 lst) # word_rsplit_aux (List.drop 8 lst) n"

definition word_rcat_k :: "u8 list \<Rightarrow> u64" where
  "word_rcat_k lst = of_bl (List.concat (List.map to_bl lst))"

definition word_rsplit :: "'a :: len word \<Rightarrow> 'b :: len word list" where
  "word_rsplit w = map word_of_int (bin_rsplit (len_of TYPE ('b)) (len_of TYPE ('a), uint w))"

definition invert_endian :: "u64 \<Rightarrow> u64" where
  "invert_endian w = word_rcat_k (List.rev (word_rsplit w))"

definition keccakf :: "u64 list \<Rightarrow> u64 list" where
  "keccakf st = List.foldl for_inner st (genlist (\<lambda>i. i) keccakf_rounds)"

definition mdlen :: "nat" where
  "mdlen = 256 div 8"

definition rsiz :: "nat" where
  "rsiz = 200 - mdlen * 2"

definition word8_to_word64 :: "u8 \<Rightarrow> u64" where
  "word8_to_word64 w = word_of_nat (unat w)"

definition update_byte :: "u8 \<Rightarrow> nat \<Rightarrow> u64 list \<Rightarrow> u64 list" where
  "update_byte i p st = setf st (p div 8) (get st (p div 8) XOR (word8_to_word64 i << (8 * (p mod 8))))"

fun sha3_update :: "u8 list \<Rightarrow> nat \<Rightarrow> u64 list \<Rightarrow> nat * u64 list" where
  "sha3_update [] pos st = (pos, st)"
| "sha3_update (c # rest) pos st = (
    if pos \<le> rsiz then sha3_update rest (pos + 1) (update_byte c pos st)
    else sha3_update rest 0 (keccakf (update_byte c pos st))
  )"

definition keccak_final :: "nat \<Rightarrow> u64 list \<Rightarrow> u8 list" where
  "keccak_final p st = (
    let st0 = update_byte (0x01) p st in
    let st1 = update_byte (0x80) (rsiz - 1) st0 in
    let st2 = List.take 4 (keccakf st1) in
    List.concat (List.map (\<lambda>x. List.rev (word_rsplit x)) st2)
  )"

definition initial_st :: "u64 list" where
  "initial_st = genlist (\<lambda>x. 0) 25"

definition initial_pos :: "nat" where
  "initial_pos = 0"

definition keccak' :: "u8 list \<Rightarrow> u8 list" where
  "keccak' input = (
    let mid = sha3_update input initial_pos initial_st in
    keccak_final (fst mid) (snd mid)
  )"

definition keccak :: "u8 list \<Rightarrow> u256" where
  "keccak input = word_rcat (keccak' input)"

lemma keccak_test1: "keccak [0x61, 0x62, 0x63] = 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
  by eval

lemma keccak_test2: "keccak [0x00, 0x00, 0x34, 0x12, 0x47, 0x11, 0x00, 0x00, 0x34, 0x12, 0x47, 0x11, 0xff, 0xff, 0xff, 0xff] 
  = 0x83f69e636b92554f91ca92ef928e6a192a28bcfc935b4a019e4b56885e42eb51"
  by eval

end