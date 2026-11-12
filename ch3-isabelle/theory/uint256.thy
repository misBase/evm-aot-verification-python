theory uint256
  imports
    EVMCommType
begin

record uint256 =
  z0 :: "u64"
  z1 :: "u64"
  z2 :: "u64"
  z3 :: "u64"

definition uint256_zero :: "uint256" where
  "uint256_zero \<equiv> \<lparr> z0 = 0, z1 = 0, z2 = 0, z3 = 0 \<rparr>"

definition uint256_one :: "uint256" where
  "uint256_one \<equiv> \<lparr> z0 = 1, z1 = 0, z2 = 0, z3 = 0 \<rparr>"

definition uint256_two :: "uint256" where
  "uint256_two \<equiv> \<lparr> z0 = 2, z1 = 0, z2 = 0, z3 = 0 \<rparr>"

definition uint256_three :: "uint256" where
  "uint256_three \<equiv> \<lparr> z0 = 3, z1 = 0, z2 = 0, z3 = 0 \<rparr>"

definition uint256_32 :: "uint256" where
  "uint256_32 \<equiv> \<lparr> z0 = 32, z1 = 0, z2 = 0, z3 = 0 \<rparr>"

definition uint256_2_64 :: "uint256" where
  "uint256_2_64 \<equiv> \<lparr> z0 = 0, z1 = 1, z2 = 0, z3 = 0 \<rparr>"

definition uint256_max :: "uint256" where
  "uint256_max \<equiv> \<lparr> z0 = 2^64 -1, z1 = 2^64 -1, z2 = 2^64 -1, z3 = 2^64 -1  \<rparr>"

definition Isuint64 ::"uint256 \<Rightarrow> bool" where
  "Isuint64 z \<equiv> (z1 z = 0 \<and> z2 z = 0 \<and> z3 z = 0)"

definition IsZero :: "uint256 \<Rightarrow> bool" where
  "IsZero z \<equiv> (z0 z OR z1 z OR z2 z OR z3 z) = 0"

definition Sign :: "uint256 \<Rightarrow> int" where
  "Sign x = (
    if IsZero x then 0
    else if z3 x < 0x8000000000000000 then 1
    else -1
  )"

definition getword :: "uint256 \<Rightarrow> nat \<Rightarrow> u64" where
"getword x n = (
  if n = 3 then z3 x
  else if n = 2 then z2 x
  else if n = 1 then z1 x
  else if n = 0 then z0 x
  else 0
)"

definition Add64_carry ::"u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
" Add64_carry x y c = (
    let 
      sum = x + y + c;
      carry_out = ((x AND y) OR ((x OR y) AND (NOT sum))) >> 63 
  in
    (sum, carry_out)  
)"

definition uint256_add ::"uint256 \<Rightarrow> uint256 \<Rightarrow> uint256"(infix "+\<^sub>u" 50) where
" uint256_add x y = (
    let (s0, c0) = Add64_carry (z0 x) (z0 y) 0 in
    let (s1, c1) = Add64_carry (z1 x) (z1 y) c0 in
    let (s2, c2) = Add64_carry (z2 x) (z2 y) c1 in
    let (s3, _)  = Add64_carry (z3 x) (z3 y) c2 in
    \<lparr> z0 = s0, z1 = s1, z2 = s2, z3 = s3 \<rparr>
)"


definition Sub64_borrow :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
"Sub64_borrow x y borrow = (
  let 
    diff = x - y - borrow;
    borrow_out = (((NOT x) AND y) OR ((NOT (x XOR y)) AND diff)) >> 63
  in 
    (diff, borrow_out)
)"

definition uint256_sub :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "-\<^sub>u" 50) where
"x -\<^sub>u y = (
  let 
    (d0, c0) = Sub64_borrow (z0 x) (z0 y) 0;
    (d1, c1) = Sub64_borrow (z1 x) (z1 y) c0;
    (d2, c2) = Sub64_borrow (z2 x) (z2 y) c1;
    (d3, _) = Sub64_borrow (z3 x) (z3 y) c2
  in 
    \<lparr> z0 = d0, z1 = d1, z2 = d2, z3 = d3 \<rparr>
)"

definition Neg :: "uint256 \<Rightarrow> uint256" where
  "Neg x = uint256_sub uint256_zero x"

definition mul64 :: "u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
"mul64 x y =(
  let
  mask32 = (1 << 32) -1;
  x0 = x AND mask32;
  x1 = x >> 32;
  y0 = y AND mask32;
  y1 = y >> 32;
  w0 = x0 * y0;
  t = x1*y0 + (w0 >> 32);
  w1 = t AND mask32;
  w2 = t >> 32;
  w1' = w1 + x0 * y1;
  hi = x1*y1 + w2 + (w1' >> 32);
  lo = x * y  
in
   (hi , lo)
)"

definition umulHop :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
"umulHop z x y = (
  let 
    (hi, lo) = mul64 x y;
    (lo, carry) = Add64_carry lo z 0;
    (hi, _) = Add64_carry hi 0 carry
  in 
    (hi, lo)
  )"

definition umulStep :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
"umulStep z x y carry = (
  let 
    (hi, lo) = mul64 x y; 
    (lo, carry1) = Add64_carry lo carry 0;
    (hi, carry2) = Add64_carry hi 0 carry1;
    (lo, carry3) = Add64_carry lo z 0;
    (hi, _) = Add64_carry hi 0 carry3
  in 
    (hi, lo)
)"

definition uint256_mul :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "*\<^sub>u" 50) where
"x *\<^sub>u y = (
  let 
    x0 = z0 x; x1 = z1 x; x2 = z2 x; x3 = z3 x;
    y0 = z0 y; y1 = z1 y; y2 = z2 y; y3 = z3 y;

    (carry0, z0) = mul64 x0 y0;
    (carry0, res1) = umulHop carry0 x1 y0;
    (carry0, res2) = umulHop carry0 x2 y0;
    
    (carry1, z1) = umulHop res1 x0 y1;
    (carry1, res2) = umulStep res2 x1 y1 carry1;
    
    (carry2, z2) = umulHop res2 x0 y2;
    
    z3 = x3*y0 + x2*y1 + x0*y3 + x1*y2 + carry0 + carry1 + carry2
  in 
    \<lparr> z0 = z0, z1 = z1, z2 = z2, z3 = z3 \<rparr>
)"

definition uint256_to_int :: "uint256 \<Rightarrow> int" where
"uint256_to_int x = (
  let 
    n0 = uint (z0 x);
    n1 = uint (z1 x);
    n2 = uint (z2 x);
    n3 = uint (z3 x)
  in
    n0 + (n1 << 64) + (n2 << 128) + (n3 << 192)
)"


definition int_to_uint256 :: "int \<Rightarrow> uint256" where
"int_to_uint256 i = (
    \<lparr>  z0 = word_of_int (i mod 2^64),
       z1 = word_of_int ((i >> 64) mod 2^64),
       z2 = word_of_int ((i >> 128) mod 2^64),
       z3 = word_of_int ((i >> 192) mod 2^64) \<rparr>
)"



definition word256_to_uint256 :: "u256 \<Rightarrow> uint256" where
"word256_to_uint256 x \<equiv> int_to_uint256 (uint x)"


definition uint256_to_word256 :: "uint256 \<Rightarrow> u256" where
"uint256_to_word256 x \<equiv>word_of_int (uint256_to_int x)"

definition uint256_lt :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix "<\<^sub>u" 50) where
"x <\<^sub>u y = (
  let (_, c0) = Sub64_borrow (z0 x) (z0 y) 0 ;
      (_, c1) = Sub64_borrow (z1 x) (z1 y) c0 ;
      (_, c2) = Sub64_borrow (z2 x) (z2 y) c1 ;
      (_, c3) = Sub64_borrow (z3 x) (z3 y) c2
  in
  c3 \<noteq> 0
)
"

definition uint256_slt :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix "<\<^sub>s" 50) where
  "x <\<^sub>s y \<equiv> (
    let zSign = Sign x;
        ySign = Sign y
    in
      if zSign \<ge> 0 \<and> ySign < 0 then
        False
      else if zSign < 0 \<and> ySign \<ge> 0 then
        True  
      else
        x <\<^sub>u y
  )"


value " Sub64_borrow (z0 uint256_one) (z0 uint256_zero) 0"
value " Sub64_borrow (z1 uint256_one) (z1 uint256_zero) 1"
value " Sub64_borrow (z2 uint256_one) (z2 uint256_zero) 1"
value " Sub64_borrow (z3 uint256_one) (z0 uint256_zero) 3"


definition uint256_eq :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix "=\<^sub>u" 50) where
"x =\<^sub>u y \<longleftrightarrow> (z0 x = z0 y \<and> z1 x = z1 y \<and> z2 x = z2 y \<and> z3 x = z3 y)"

definition uint256_gt :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix ">\<^sub>u" 50) where
"x >\<^sub>u y \<longleftrightarrow> y <\<^sub>u x"

definition uint256_sgt :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix ">\<^sub>s" 50) where
  "x >\<^sub>s y \<equiv> (
    let xSign = Sign x;
        ySign = Sign y
    in
      if xSign \<ge> 0 \<and> ySign < 0 then
        True
      else if xSign < 0 \<and> ySign \<ge> 0 then
        False  
      else
        x >\<^sub>u y
  )"

definition Byte :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "Byte z n = (
    let index = unat (z0 n) 
in
   if uint256_to_int n \<ge> 32 then
      uint256_zero
    else(
      let word_index = 3 - (index div 8); 
          number = getword z word_index; 
          offset = (index mod 8) * 8;
          byte_val = (number >> (56 - offset)) AND 0xFF
     in
      \<lparr> z0 = byte_val, z1 = 0, z2 = 0, z3 = 0 \<rparr>
))"

definition uint256_le :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix "\<le>\<^sub>u" 50) where
"x \<le>\<^sub>u y \<longleftrightarrow> (x <\<^sub>u y \<or> x =\<^sub>u y)"

definition uint256_ge :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix "\<ge>\<^sub>u" 50) where
"x \<ge>\<^sub>u y \<longleftrightarrow> y \<le>\<^sub>u x"

definition uint256_ne :: "uint256 \<Rightarrow> uint256 \<Rightarrow> bool" (infix "\<noteq>\<^sub>u" 50) where
"x \<noteq>\<^sub>u y \<longleftrightarrow> \<not>(x =\<^sub>u y)"


definition uint256_or :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "OR\<^sub>u" 50) where
"x OR\<^sub>u y = \<lparr> 
  z0 = z0 x OR z0 y,
  z1 = z1 x OR z1 y,
  z2 = z2 x OR z2 y,
  z3 = z3 x OR z3 y
\<rparr>"

definition uint256_and :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "AND\<^sub>u" 50) where
"x AND\<^sub>u y = \<lparr> 
  z0 = z0 x AND z0 y,
  z1 = z1 x AND z1 y,
  z2 = z2 x AND z2 y,
  z3 = z3 x AND z3 y
\<rparr>"

definition uint256_xor :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "XOR\<^sub>u" 50) where
"x XOR\<^sub>u y = \<lparr> 
  z0 = z0 x XOR z0 y,
  z1 = z1 x XOR z1 y,
  z2 = z2 x XOR z2 y,
  z3 = z3 x XOR z3 y
\<rparr>"

definition uint256_not :: "uint256 \<Rightarrow> uint256" ("NOT\<^sub>u") where
"NOT\<^sub>u x = \<lparr> 
  z0 = NOT (z0 x),
  z1 = NOT (z1 x),
  z2 = NOT (z2 x),
  z3 = NOT (z3 x)
\<rparr>"

definition bytes_to_uint256 :: "u8 list \<Rightarrow> uint256" where
  "bytes_to_uint256 bytes = (
    let grouped = [take 8 bytes, take 8 (drop 8 bytes), 
                   take 8 (drop 16 bytes), take 8 (drop 24 bytes)];
       words = map word_rcat grouped
    in \<lparr> z0 = words!0, z1 = words!1, z2 = words!2, z3 = words!3 \<rparr>
  )"

definition uint256_to_word160 :: "uint256 \<Rightarrow> 160 word" where
  "uint256_to_word160 z = (
    let
      hi32 = uint (z2 z) mod 2^32;
      mid64 = uint (z1 z);
      lo64 = uint (z0 z);
      
      combined = (hi32 << 128) + (mid64 << 64) + lo64;
      
      word160 = word_of_int combined
    in
      word160
  )"

definition word160_to_uint256 :: "160 word \<Rightarrow> uint256" where
"word160_to_uint256 w = (
  let
    val = uint w;
    hi32 = (val >> 128) mod 2^32;
    mid64 = (val >> 64) mod 2^64;
    lo64 = val mod 2^64
  in
    \<lparr> z0 = word_of_int lo64,
       z1 = word_of_int mid64,
       z2 = word_of_int hi32,
       z3 = 0 \<rparr>
)"


definition uint256_to_byte :: "uint256 \<Rightarrow> byte" where
  "uint256_to_byte z = (
    let
      word8 =  uint (z0 z) mod 2^8;
      byte = word_of_int word8
    in
      byte
  )"


definition uint256_succ :: "uint256 \<Rightarrow> uint256" where
  "uint256_succ x = (
    if x = \<lparr> z0 = 2^64-1, z1 = 2^64-1, z2 = 2^64-1, z3 = 2^64-1 \<rparr> then 
      uint256_zero
    else 
      uint256_add x \<lparr> z0 = 1, z1 = 0, z2 = 0, z3 = 0 \<rparr>
  )"

definition dLen :: "uint256 \<Rightarrow> nat"where
"dLen x = (
  if z3 x \<noteq> 0 then 4 
  else if z2 x \<noteq> 0 then 3 
  else if z1 x \<noteq> 0 then 2
  else if z0 x \<noteq> 0 then 1
  else 0
)"

definition uLen :: "uint256 \<Rightarrow> nat"where
"uLen x = dLen x + 1"

definition len8tab :: "8 word \<Rightarrow> nat" where
  "len8tab x \<equiv> (
    if x = 0 then 0
    else if x \<ge> 128 then 8
    else if x \<ge> 64 then 7
    else if x \<ge> 32 then 6
    else if x \<ge> 16 then 5
    else if x \<ge> 8 then 4
    else if x \<ge> 4 then 3
    else if x \<ge> 2 then 2
    else 1
  )"

definition Len64 :: " u64 \<Rightarrow> nat" where
"Len64 x = (
  let   
  (n1,x1) = if x \<ge> (1 << 32) then (32, x >> 32) else (0, x);
  (n2,x2) = if x1 \<ge> (1 << 16) then (16, x1 >> 16) else (0, x1);
  (n3,x3) = if x2 \<ge> (1 << 8) then (8, x2 >> 8) else (0, x2)
  in
  n1 + n2 + n3 + len8tab (ucast x3)
)"

definition BitLen ::"uint256 \<Rightarrow> nat"where
"BitLen x = (
  if z3 x \<noteq> 0 then 192+(Len64 (z3 x)) 
  else if z2 x \<noteq> 0 then 128+(Len64 (z2 x))
  else if z1 x \<noteq> 0 then 64+(Len64 (z1 x))
else Len64 (z0 x)
)"

definition LeadingZeros64 :: "u64 \<Rightarrow> nat" where
"LeadingZeros64 x = 64 - (Len64 x)"

definition getword_u :: "uint256 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64" where
"getword_u u n u4 = (
  if (n < 4) then (getword u n) else u4
)
"

definition dnStorage :: "uint256 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint256" where
"dnStorage d l shift = (
  \<lparr> z0 = (z0 d << shift),
    z1 = (if l \<ge> 2 then (z1 d << shift) OR (z0 d >> (64 - shift)) else 0),
    z2 = (if l \<ge> 3 then (z2 d << shift) OR (z1 d >> (64 - shift)) else 0),
    z3 = (if l \<ge> 4 then (z3 d << shift) OR (z2 d >> (64 - shift)) else 0)
  \<rparr>
)"

definition normalize_u :: "uint256 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint256 \<times> u64" where
"normalize_u u ulen shift = (
  dnStorage u (if ulen < 4 then ulen + 1 else 4) shift,
  if ulen = 4 then getword u (ulen - 1) >> (64 - shift) else 0
)"

fun adjust_q_nat :: "nat \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
"adjust_q_nat 0 r yn0 yn1 un two32 = (0, r)" |
"adjust_q_nat (Suc n) r yn0 yn1 un two32 = (
  if (of_nat (Suc n)) < two32 \<and> (of_nat (Suc n)) * yn0 \<le> two32 * r + un then
      ((of_nat (Suc n)), r)
    else
      let r' = r + yn1 in
        if r' \<ge> two32 then (of_nat n, r')
        else adjust_q_nat n r' yn0 yn1 un two32)"
  
definition adjust_q :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
"adjust_q q r yn0 yn1 un two32 = (adjust_q_nat (unat q) r yn0 yn1 un two32)"

definition Div64 :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64) option" where
"Div64 hi lo y = (
  if y = 0 then None
  else if y \<le> hi then None
  else if hi = 0 then Some (lo div y, lo mod y)
  else
    let 
      s = LeadingZeros64 y;
      y_shifted = y << s;
      two32 = (1 << 32);
      mask32 = two32 - 1;
      yn1 = y_shifted >> 32;
      yn0 = y_shifted AND mask32;
      un32 = (hi << s) OR (lo >> (64 - s));
      un10 = lo << s;
      un1 = un10 >> 32;
      un0 = un10 AND mask32;
      q1 = un32 div yn1;
      rhat = un32 - q1 * yn1;
      
      (q1_adj, _) = adjust_q q1 rhat yn0 yn1 un1 two32;
      
      un21 = un32 * two32 + un1 - q1_adj * y_shifted;
      q0 = un21 div yn1;
      rhat' = un21 - q0 * yn1;
      (q0_adj, _) = adjust_q q0 rhat' yn0 yn1 un0 two32
    in
      Some (q1_adj * two32 + q0_adj, 
           (un21 * two32 + un0 - q0_adj * y_shifted) >> s)
)"

value "NOT (9223372036854775808 ::u64) "
value "9223372036854775808 \<le> (9223372036854775807::u64) "
value "Div64 0 10 2"       (* Some (5, 0) *)
value "0xFFFFFFFF + (0xFFFFFFFF::u64)"

(*
value "Div64 9223372036854775807 (2^64-1) 9223372036854775808"
*)

definition reciprocal2by1 :: "u64 \<Rightarrow> u64" where
"reciprocal2by1 d = (
  case Div64 (NOT d) (2^64-1) d of
    Some (reciprocal, _) \<Rightarrow> reciprocal
    | None \<Rightarrow> undefined
)"

definition update_word_uint256 :: "uint256 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> uint256" where
  "update_word_uint256 num pos new_val \<equiv>
    (if pos = 0 then \<lparr> z0 = new_val, z1 = z1 num, z2 = z2 num, z3 = z3 num \<rparr>
     else if pos = 1 then \<lparr> z0 = z0 num, z1 = new_val, z2 = z2 num, z3 = z3 num \<rparr>
     else if pos = 2 then \<lparr> z0 = z0 num, z1 = z1 num, z2 = new_val, z3 = z3 num \<rparr>
     else if pos = 3 then \<lparr> z0 = z0 num, z1 = z1 num, z2 = z2 num, z3 = new_val \<rparr>
     else num)"

definition update_word_u4 :: "uint256 \<Rightarrow> u64 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> uint256 \<times> u64"where
"update_word_u4 num u4 pos new_val = (
  if pos = 4 then (num,new_val) else((update_word_uint256 num pos new_val), u4)
)
"

definition udivrem2by1 :: "u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> (u64 \<times> u64)" where
"udivrem2by1 uh ul d reciprocal = (
  let 
    (qh, ql) = mul64 reciprocal uh;
    (ql, carry) = Add64_carry ql ul 0;
    (qh, _) = Add64_carry qh uh carry;
    qh_adj = qh + 1;  
    r = ul - qh_adj * d;
    (qh1, r1) = (
      if r > ql then
        (qh_adj - 1, r + d)
      else
        (qh_adj, r)
    );
    (qh_final, r_final) = (
      if r1 \<ge> d then
        (qh1 + 1, r1 - d)
      else
        (qh1, r1)
    )
  in
    (qh_final, r_final)
)"

fun subMulTo_aux :: 
  "uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<times> uint256 \<times> u64" 
where
  "subMulTo_aux x u4 y multiplier 0 j borrow = (borrow,x,u4)"|
  "subMulTo_aux x u4 y multiplier (Suc n) j borrow = (
      let 
        x_i = getword_u x ((dLen y - (Suc n))+j) u4;
        (s, carry1) = Sub64_borrow x_i borrow 0;
        y_i = getword y (dLen y - (Suc n));
        (ph, pl) = mul64 y_i multiplier;
        
        (t, carry2) = Sub64_borrow s pl 0;
        
        (new_x,new_u4) = update_word_u4 x u4 ((dLen y - (Suc n))+j) t;
        new_borrow = ph + carry1 + carry2
      in 
        subMulTo_aux new_x new_u4 y multiplier n j new_borrow 
  )"



definition subMulTo :: "uint256 \<Rightarrow>u64 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<times> uint256 \<times> u64" where
"subMulTo x u4 y j multiplier = subMulTo_aux x u4 y multiplier (dLen y) j 0"

fun addTo_aux :: 
  "uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow>  nat \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<times> uint256 \<times> u64" 
where
  "addTo_aux x u4 y 0 j carry = (carry,x,u4)"|
    "addTo_aux x u4 y (Suc n) j carry = (
      let 
        x_i = getword_u x ((dLen y - (Suc n))+j) u4;
        y_i = getword y (dLen y - (Suc n));
        (s, new_carry) = Add64_carry x_i y_i carry;
        (x_new,u4_new) = update_word_u4 x u4 ((dLen y - (Suc n)) + j) s
      in 
        addTo_aux x_new u4_new y n j new_carry 
  )"


definition addTo :: "uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> u64 \<times> uint256 \<times> u64" where
"addTo x u4 y j = addTo_aux x u4 y (dLen y) j 0"

fun udivrem_knuth_loop :: "nat \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> uint256 \<times> uint256 \<times> u64" 
where
  "udivrem_knuth_loop 0 u u4 d dh dl reciprocal quot = (
      let
        u2 = getword_u u (0 + dLen d) u4;
        u1 = getword u (0 + dLen d - 1);
        u0 = getword u (0 + dLen d - 2);
        (qhat, rhat) = (
          if u2 \<ge> dh then 
            (2^64-1 , 0)
          else 
            udivrem2by1 u2 u1 dh reciprocal
        );
        
        qhat_adj = (
          if u2 \<ge> dh then
            qhat
          else
            let (ph, pl) = mul64 qhat dl in
            if ph > rhat \<or> (ph = rhat \<and> pl > u0) then
              qhat - 1
            else
              qhat
        );
        
         (borrow,u_s,u4_s) = subMulTo u u4 d 0 qhat_adj;
         (u_new,u4_new) = update_word_u4 u_s u4_s (0+dLen d) (u2-borrow);
         (u_final,u4_final) = (
          if u2 < borrow then
            let
            (carry,u_add,u4_add) = addTo u_new u4_new d 0
            in
             update_word_u4 u_add u4_add (0+dLen d) (u2 - borrow + carry)
          else
            (u_new,u4_new)
        );
        qhat_final = (
          if u2 < borrow then
             qhat_adj - 1
          else
            qhat_adj
        );        
        quot_new = update_word_uint256 quot 0 qhat_final
      in
        (quot_new,u_final,u4_final)
  )"|
 "udivrem_knuth_loop (Suc n) u u4 d dh dl reciprocal quot = (
      let
        u2 = getword_u u ((Suc n) + dLen d) u4;
        u1 = getword u ((Suc n) + dLen d - 1);
        u0 = getword u ((Suc n) + dLen d - 2);
        (qhat, rhat) = (
          if u2 \<ge> dh then 
            (2^64-1 , 0)
          else 
            udivrem2by1 u2 u1 dh reciprocal
        );
        
        qhat_adj = (
          if u2 \<ge> dh then
            qhat
          else
            let (ph, pl) = mul64 qhat dl in
            if ph > rhat \<or> (ph = rhat \<and> pl > u0) then
              qhat - 1
            else
              qhat
        );
        
         (borrow,u_s,u4_s) = subMulTo u u4 d (Suc n) qhat_adj;
         (u_new,u4_new) = update_word_u4 u_s u4_s ((Suc n)+dLen d) (u2-borrow);
         (u_final,u4_final) = (
          if u2 < borrow then
            let
            (carry,u_add,u4_add) = addTo u_new u4_new d (Suc n)
            in
             update_word_u4 u_add u4_add ((Suc n)+dLen d) (u2 - borrow + carry)
          else
            (u_new,u4_new)
        );
        qhat_final = (
          if u2 < borrow then
             qhat_adj - 1
          else
            qhat_adj
        );        
        quot_new = update_word_uint256 quot (Suc n) qhat_final
      in
        udivrem_knuth_loop n u_final u4_final d dh dl reciprocal quot_new
  )"


definition udivremKnuth :: "uint256 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> uint256 \<times> uint256 \<times> u64" where
"udivremKnuth quot u u4 d ulen =(
  let 
  dh = getword d (dLen d - 1);
  dl = getword d (dLen d - 2);
  reciprocal = reciprocal2by1 dh
  in
  udivrem_knuth_loop (ulen - dLen d) u u4 d dh dl reciprocal quot
)"

fun udivremBy1_loop ::"uint256 \<Rightarrow> uint256 \<Rightarrow>nat \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> uint256 \<times> u64"where
"udivremBy1_loop quot u 0 rem d reciprocal = (
  let u_j = getword u 0;
  (quot_j,rem_update) = udivrem2by1 rem u_j d reciprocal;
  quot_update = update_word_uint256 quot 0 quot_j
  in
  (quot_update,rem_update)
)"|
"udivremBy1_loop quot u (Suc n) rem d reciprocal = (
  let u_j = getword u (Suc n);
  (quot_j,rem_update) = udivrem2by1 rem u_j d reciprocal;
  quot_update = update_word_uint256 quot (Suc n) quot_j
  in
  udivremBy1_loop quot_update u n rem_update d reciprocal 
)"

definition udivremBy1 :: "uint256 \<Rightarrow> uint256 \<Rightarrow> nat \<Rightarrow> u64 \<Rightarrow> u64 \<Rightarrow> uint256 \<times> u64"where
"udivremBy1 quot u ulen d u4 =(
  let reciprocal = reciprocal2by1 d;
      rem = getword_u u ulen u4
  in
  udivremBy1_loop quot u (ulen - 1) rem d reciprocal
)"

definition SetUint64 ::"u64 \<Rightarrow> uint256"where
"SetUint64 x = \<lparr> z0 = x, z1 = 0, z2 = 0, z3 = 0\<rparr>" 

fun rem_loop :: "uint256 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint256"where
"rem_loop rem un u4 0 cnt shift = (
  let un_i = getword_u un cnt u4
  in update_word_uint256 rem cnt (un_i >> shift)
)"|
"rem_loop rem un u4 i cnt shift = (
let
  un_i = getword_u un (cnt-i) u4;
  un_i1 = getword_u un ((cnt - i)+1) u4;
  rem_i = ((un_i >> shift) OR ((un_i1 << (64 - shift))));
  rem_update = update_word_uint256 rem (cnt-i) rem_i
  in
  rem_loop rem_update un u4 (i-1) cnt shift
)"


definition udivrem :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<times> uint256" where
"udivrem quot u d = ( 
 let 
  dlen = dLen d;
  shift =  LeadingZeros64 (getword d (dlen-1));
  dn = dnStorage d dlen shift;
  ulen = dLen u;
  (un,u4) = normalize_u u ulen shift;
  rem = uint256_zero
  in
(
  if ulen < dlen then (quot,u) else
  if dlen = 1 then 
  (
  let (quot_new,r) = udivremBy1 quot un ulen (getword dn 0) u4;
      rem_new = SetUint64 (r >> shift)
  in
  (quot_new,rem_new)
  )  
  else
( 
  let (quot_new,un_new,u4_new)= udivremKnuth quot un u4 dn ulen ;
      rem_new = rem_loop rem un_new u4_new (dlen-1) (dlen-1) shift
  in                                      
  (quot_new,rem_new)
)
)
)"

definition uint256_div :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "div\<^sub>u" 50) where
"x div\<^sub>u y = (
  if y = uint256_zero then 
    uint256_zero 
  else if x <\<^sub>u y then 
    uint256_zero 
  else if x = y then
    uint256_one
  else if Isuint64 x then 
    let x64 = z0 x;
        y64 = z0 y;
        result = x64 div y64 
    in
      \<lparr> z0 = result, z1 = 0, z2 = 0, z3 = 0 \<rparr>
  else
    let 
    (quot,rem) = udivrem uint256_zero x y
    in
      quot
)"

definition SDiv :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "SDiv n d = (
      let n_sign = Sign n;
          d_sign = Sign d
      in
        if n_sign > 0 then (
          if d_sign > 0 then
            n div\<^sub>u d
          else
            Neg (n div\<^sub>u (Neg d))
        )
        else if d_sign < 0 then
          (Neg n) div\<^sub>u (Neg d)
        else
          Neg ((Neg n) div\<^sub>u d)
  )"

value "SDiv \<lparr> z0 = 128, z1 = 0, z2 = 0, z3 = 0 \<rparr>  \<lparr> z0 = 127, z1 = 0, z2 = 0, z3 = 0 \<rparr>"

definition Mod :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "mod\<^sub>u" 50) where
  "x mod\<^sub>u y = (
    if IsZero y \<or> x =\<^sub>u y then
      uint256_zero
    else if x <\<^sub>u y then
      x
    else if Isuint64 x then
      let x64 = z0 x;
          y64 = z0 y;
          result = x64 mod y64
      in
        \<lparr> z0 = result, z1 = 0, z2 = 0, z3 = 0 \<rparr>
    else
      let (quot, rem) = udivrem uint256_zero x y
      in
        rem
  )"

definition SMod :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "smod\<^sub>u" 50) where
  "x smod\<^sub>u y = (
    let xs = Sign x;
        ys = Sign y;
        x_abs = (if xs = -1 then Neg x else x);
        y_abs = (if ys = -1 then Neg y else y);
        result = x_abs mod\<^sub>u y_abs
    in
      if xs = -1 then Neg result else result
  )"

value "uint256_zero div\<^sub>u uint256_zero"

value "\<lparr> z0 = 10, z1 = 0, z2 = 0, z3 = 0 \<rparr> div\<^sub>u \<lparr> z0 = 20, z1 = 0, z2 = 0, z3 = 0 \<rparr>"

value "\<lparr> z0 = 100, z1 = 0, z2 = 0, z3 = 0 \<rparr> div\<^sub>u \<lparr> z0 = 5, z1 = 0, z2 = 0, z3 = 0 \<rparr>"  

(*
value "\<lparr> z0 = 0, z1 = 1, z2 = 0, z3 = 0 \<rparr> div\<^sub>u \<lparr> z0 = 1, z1 = 0, z2 = 0, z3 = 0 \<rparr>"
*)

definition squared :: "uint256 \<Rightarrow> uint256" where
"squared x = (
  let
  (carry0,res0) = mul64 (z0 x) (z0 x);
  (carry0_new,res1) = umulHop carry0 (z0 x) (z1 x);
  (carry0_final,res2) = umulHop carry0_new (z0 x) (z2 x);
  (carry1,res1_new) = umulHop res1 (z0 x) (z1 x);
  (carry1_new,res2_new) = umulStep res2 (z1 x) (z1 x) carry1;
  (carry2,res2_final) = umulHop res2_new (z0 x) (z2 x);
  res3 = 2*((z0 x) * (z3 x) + (z1 x) * (z2 x)) + carry0_final + carry1_new + carry2
  in
  \<lparr>z0 = res0, z1 = res1_new, z2 = res2_final, z3 = res3 \<rparr>
)"

fun Exp_aux :: "uint256 \<Rightarrow> uint256 \<Rightarrow> u64 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uint256 \<times>  uint256 \<times> nat" where
  "Exp_aux res multiplier word 0 curBit = (res,multiplier,curBit)" |
  "Exp_aux res multiplier word bits_to_process 0 = (res,multiplier,0)" |
  "Exp_aux res multiplier word (Suc bits_to_process) (Suc curBit) = (
    let 
      new_res = if (word AND 1 = 1) then (res *\<^sub>u multiplier) else res;
      new_multiplier = squared multiplier;
      new_word = word >> 1
    in
      Exp_aux new_res new_multiplier new_word bits_to_process curBit 
  )"


definition Exp :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" (infix "**\<^sub>u" 50) where
  "base **\<^sub>u exponent = (
    let 
      res = uint256_one;
      multiplier = base;
      expBitLen = BitLen exponent;
      even = (z0 base AND 1 = 0)
    in
      if even \<and> expBitLen > 8 then
        uint256_zero
      else
        let
          (res1, multiplier1, curBit1) = 
            Exp_aux res multiplier (z0 exponent) 64 expBitLen;
          (res2, multiplier2, curBit2) = 
            Exp_aux res1 multiplier1 (z1 exponent) 64 curBit1;
          (res3, multiplier3, curBit3) = 
              Exp_aux res2 multiplier2 (z2 exponent) 64 curBit2;
          (res4, _, _) = 
              Exp_aux res3 multiplier3 (z3 exponent) 64 curBit3
        in
          res4
  )"

definition GtUint64 :: "uint256 \<Rightarrow> u64 \<Rightarrow> bool" where
  "GtUint64 z n \<equiv> z0 z > n \<or> (z1 z OR z2 z OR z3 z) \<noteq> 0"

definition extend_sign :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
  "extend_sign x byteNum = (
    if GtUint64 byteNum 30 then x
    else
      let e = z0 byteNum;
          sign_word_index = unat (e >> 3);
          sign_byte_index = unat (e AND 7);
          sign_word = getword x sign_word_index;
          sign_byte_offset = sign_byte_index * 8;
          sign_byte = sign_word >> sign_byte_offset;
          is_negative = (sign_byte AND 0x80) \<noteq> 0;
          sext_byte = (if is_negative then 
                      (0xFFFFFFFFFFFFFF00 OR (sign_byte AND 0xFF))  
                      else 
                        sign_byte AND 0x00000000000000FF                      
                      );
          sext = sext_byte << sign_byte_offset;
          sign_mask = 0xFFFFFFFFFFFFFFFF << sign_byte_offset;
          value = sign_word AND (NOT sign_mask);
          new_sign_word = sext OR value;
          sign_ex = (if is_negative then 0xFFFFFFFFFFFFFFFF else 0)
      in
        (if sign_word_index = 0 then
          \<lparr> z0 = new_sign_word, z1 = sign_ex, z2 = sign_ex, z3 = sign_ex \<rparr>
         else if sign_word_index = 1 then
          \<lparr> z0 = z0 x , z1 = new_sign_word, z2 = sign_ex, z3 = sign_ex \<rparr>
         else if sign_word_index = 2 then
          \<lparr> z0 = z0 x , z1 =z1 x, z2 =  new_sign_word, z3 = sign_ex \<rparr>
         else                             
          \<lparr> z0 = z0 x , z1 =z1 x, z2 =  z2 x, z3 = new_sign_word \<rparr>
  )
  )"

value "extend_sign  \<lparr> z0 = 2, z1 = 0, z2 = 0, z3 = 0\<rparr>  \<lparr> z0 = 28, z1 = 0, z2 = 0, z3 = 0 \<rparr>"


definition uint256_addmod :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
"uint256_addmod x y m = (
  if IsZero m then  
    uint256_zero
  else
    if z3 m \<noteq> 0 \<and> z3 x \<le> z3 m \<and> z3 y \<le> z3 m then
      let
        (tmpX0, gteC1_0) = Sub64_borrow (z0 x) (z0 m) 0;
        (tmpX1, gteC1_1) = Sub64_borrow (z1 x) (z1 m) gteC1_0;
        (tmpX2, gteC1_2) = Sub64_borrow (z2 x) (z2 m) gteC1_1;
        (tmpX3, gteC1) = Sub64_borrow (z3 x) (z3 m) gteC1_2;
        
        x_reduced = (if gteC1 = 0 then \<lparr>z0 = tmpX0, z1 = tmpX1, z2 = tmpX2, z3 = tmpX3\<rparr> else x);
        
        (tmpY0, gteC2_0) = Sub64_borrow (z0 y) (z0 m) 0;
        (tmpY1, gteC2_1) = Sub64_borrow (z1 y) (z1 m) gteC2_0;
        (tmpY2, gteC2_2) = Sub64_borrow (z2 y) (z2 m) gteC2_1;
        (tmpY3, gteC2) = Sub64_borrow (z3 y) (z3 m) gteC2_2;
        
        y_reduced = (if gteC2 = 0 then \<lparr>z0 = tmpY0, z1 = tmpY1, z2 = tmpY2, z3 = tmpY3\<rparr> else y);
        
        (sum0, c1_0) = Add64_carry (z0 x_reduced) (z0 y_reduced) 0;
        (sum1, c1_1) = Add64_carry (z1 x_reduced) (z1 y_reduced) c1_0;
        (sum2, c1_2) = Add64_carry (z2 x_reduced) (z2 y_reduced) c1_1;
        (sum3, c1) = Add64_carry (z3 x_reduced) (z3 y_reduced) c1_2;
        
        res = \<lparr>z0 = sum0, z1 = sum1, z2 = sum2, z3 = sum3\<rparr>;
        
        (tmp0, c2_0) = Sub64_borrow sum0 (z0 m) 0;
        (tmp1, c2_1) = Sub64_borrow sum1 (z1 m) c2_0;
        (tmp2, c2_2) = Sub64_borrow sum2 (z2 m) c2_1;
        (tmp3, c2) = Sub64_borrow sum3 (z3 m) c2_2
      in
        if c1 = 0 \<and> c2 \<noteq> 0 then
          res
        else
          \<lparr>z0 = tmp0, z1 = tmp1, z2 = tmp2, z3 = tmp3\<rparr>
    
    else
      let
        sum = x +\<^sub>u y
      in
      sum mod\<^sub>u m
)"  

definition LtUint64 :: "uint256 \<Rightarrow> u64 \<Rightarrow> bool" where
"LtUint64 x n \<equiv> z0 x < n \<and> (z1 x OR z2 x OR z3 x =0)"

definition Lsh :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
"Lsh shift value =(
  if uint256_to_int shift \<ge> 256 then uint256_zero
  else let n = unat (z0 shift) in
  if n = 0 then value
  else if n \<ge> 192 then
    \<lparr> z0 = 0, z1 = 0, z2 = 0, z3 = z0 value << (n - 192) \<rparr>
  else if n \<ge> 128 then
    \<lparr> z0 = 0, 
       z1 = 0,
       z2 = z0 value << (n - 128),
       z3 = (z1 value << (n - 128)) OR (z0 value >> (64 - (n - 128))) \<rparr>
  else if n \<ge> 64 then
    \<lparr> z0 = 0,
       z1 = z0 value << (n - 64),
       z2 = (z1 value << (n - 64)) OR (z0 value >> (64 - (n - 64))),
       z3 = (z2 value << (n - 64)) OR (z1 value >> (64 - (n - 64))) \<rparr>
  else
    \<lparr> z0 = z0 value << n,
       z1 = (z1 value << n) OR (z0 value >> (64 - n)),
       z2 = (z2 value << n) OR (z1 value >> (64 - n)),
       z3 = (z3 value << n) OR (z2 value >> (64 - n)) \<rparr>
)"

definition Rsh :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
"Rsh shift value = (
  if uint256_to_int shift \<ge> 256 then uint256_zero
  else let n = unat (z0 shift) in
  if n = 0 then value
  else if n \<ge> 192 then
    \<lparr> z0 = z3 value >> (n - 192), z1 = 0, z2 = 0, z3 = 0 \<rparr>
  else if n \<ge> 128 then
    \<lparr> z0 = (z2 value >> (n - 128)) OR (z3 value << (64 - (n - 128))),
       z1 = z3 value >> (n - 128),
       z2 = 0,
       z3 = 0 \<rparr>
  else if n \<ge> 64 then
    \<lparr> z0 = (z1 value >> (n - 64)) OR (z2 value << (64 - (n - 64))),
       z1 = (z2 value >> (n - 64)) OR (z3 value << (64 - (n - 64))),
       z2 = z3 value >> (n - 64),
       z3 = 0 \<rparr>
  else
    \<lparr> z0 = (z0 value >> n) OR (z1 value << (64 - n)),
       z1 = (z1 value >> n) OR (z2 value << (64 - n)),
       z2 = (z2 value >> n) OR (z3 value << (64 - n)),
       z3 = z3 value >> n \<rparr>
)"

definition isBitSet :: "uint256 \<Rightarrow> nat \<Rightarrow> bool" where
"isBitSet x n \<equiv> (
  let idx = n div 64;
      bit = n mod 64;
      word = if idx = 0 then z0 x
             else if idx = 1 then z1 x
             else if idx = 2 then z2 x
             else if idx = 3 then z3 x
             else 0
  in (word AND (1 << bit)) \<noteq> 0
)"

definition SetAllOne :: "uint256" where
"SetAllOne \<equiv> \<lparr> 
  z0 = 2^64-1,
  z1 = 2^64-1, 
  z2 = 2^64-1,
  z3 = 2^64-1
\<rparr>"

definition MaxUint64:: "u64" where
"MaxUint64 \<equiv> 2^64-1"

definition SRsh :: "uint256 \<Rightarrow> uint256 \<Rightarrow> uint256" where
"SRsh shift value = (
  if \<not> (isBitSet value 255) then 
    Rsh shift value
  else if uint256_to_int shift \<ge> 256 then SetAllOne
  else
    let n = unat (z0 shift) in
    let a = (2^64-1) << (64 - ( n mod 64)) in
    if n = 0 then value
    else if n \<ge> 256 then 
      SetAllOne
    else if n \<ge> 192 then
      \<lparr> z0 = (z3 value >> (n - 192)) OR a, 
         z1 = MaxUint64, 
         z2 = MaxUint64, 
         z3 = MaxUint64 \<rparr>
    else if n \<ge> 128 then
      \<lparr> z0 = (z2 value >> (n - 128)) OR (z3 value << (64 - (n - 128))),
         z1 = (z3 value >> (n - 128)) OR a,
         z2 = MaxUint64,
         z3 = MaxUint64 \<rparr>
    else if n \<ge> 64 then 
      \<lparr> z0 = (z1 value >> (n - 64)) OR (z2 value << (64 - (n - 64))),
         z1 = (z2 value >> (n - 64)) OR (z3 value << (64 - (n - 64))),
         z2 = (z3 value >> (n - 64)) OR a,
         z3 = MaxUint64 \<rparr>
    else
      \<lparr> z0 = (z0 value >> n) OR (z1 value << (64 - n)),
         z1 = (z1 value >> n) OR (z2 value << (64 - n)),
         z2 = (z2 value >> n) OR (z3 value << (64 - n)),
         z3 = (z3 value >> n) OR a \<rparr>
)"     

end
