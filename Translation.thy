theory Translation
imports
  Firewall_Common
  Primitives
  PrimitiveMatchers
  Intermediate_Representation
begin

(* normalize matches to representation closest to simple_matcher *)

fun match_or :: "'a list \<Rightarrow> 'a match_expr" where
"match_or [] = MatchNot MatchAny" |
"match_or (x#xs) = MatchOr (Match x) (match_or xs)"

(* words wrap \<rightarrow> needs explicit check for 0 and max_word *)
value "(WordInterval (max_word + 1) max_word)::16 wordinterval"

fun normalize_ports' :: "16 word opspec \<Rightarrow> 16 wordinterval" where
"normalize_ports' (Unary (Eq p)) = (WordInterval p p)" |
"normalize_ports' (Unary (NEq p)) = wordinterval_setminus wordinterval_UNIV (WordInterval p p)" |
"normalize_ports' (Unary (GtEq p)) = (WordInterval p max_word)" |
"normalize_ports' (Unary (Gt p)) = (if (p = max_word) then Empty_WordInterval else (WordInterval (p + 1) max_word))" |
"normalize_ports' (Unary (LtEq p)) = (WordInterval 0 p)" |
"normalize_ports' (Unary (Lt p)) = (if (p = 0) then Empty_WordInterval else (WordInterval 0 (p - 1)))" |
"normalize_ports' (Binary (RangeIncl from to)) = (WordInterval from to)" |
"normalize_ports' (Binary (RangeExcl from to)) = (if (from = max_word \<or> to = 0) then Empty_WordInterval else (WordInterval (from + 1) (to -1)))" |
"normalize_ports' (Binary (RangeComp from to)) = wordinterval_setminus wordinterval_UNIV (WordInterval from to)"

value "normalize_ports' (Binary (RangeComp 80 0))"

value "0 < (0::16 word)"

lemma normalize_ports :
"match_port spec p \<longleftrightarrow> wordinterval_element p (normalize_ports' spec)"
  unfolding match_port_def using linorder_not_less
  by (induction spec rule: normalize_ports'.induct) (auto simp add: inc_le word_Suc_le minus_one_helper3 minus_one_helper5)

fun normalize_match' :: "pfcontext \<Rightarrow> common_primitive \<Rightarrow> 32 intermediate_primitive" where
"normalize_match' _ (common_primitive.Src UrpfFailed) = Unknown" |
"normalize_match' _ (common_primitive.Src (Hostspec (Address (IPv4 a)))) = (intermediate_primitive.Src (prefix_to_wordinterval a))" |
"normalize_match' _ (common_primitive.Src (Hostspec (Address (IPv6 a)))) = Unknown" | (* FIXME *)
"normalize_match' ctx (common_primitive.Src (Hostspec (Table t))) = (intermediate_primitive.Src (table_to_wordinterval_v4 (lookup_table ctx t)))" |
"normalize_match' _ (common_primitive.Src (Hostspec AnyHost)) = (intermediate_primitive.Src wordinterval_UNIV)" |
"normalize_match' ctx (common_primitive.Src (Hostspec NoRoute)) = Unknown" | (* TODO use ctx *)
"normalize_match' ctx (common_primitive.Src (Hostspec (Route r))) = Unknown" | (* TODO use ctx *)
"normalize_match' _ (common_primitive.Dst (Address (IPv4 a))) = (intermediate_primitive.Dst (prefix_to_wordinterval a))" |
"normalize_match' _ (common_primitive.Dst (Address (IPv6 a))) = Unknown" | (* FIXME *)
"normalize_match' ctx (common_primitive.Dst (Table t)) = (intermediate_primitive.Dst (table_to_wordinterval_v4 (lookup_table ctx t)))" |
"normalize_match' _ (common_primitive.Dst AnyHost) = (intermediate_primitive.Dst wordinterval_UNIV)" |
"normalize_match' ctx (common_primitive.Dst NoRoute) = Unknown" | (* TODO use ctx *)
"normalize_match' ctx (common_primitive.Dst (Route r)) = Unknown" | (* TODO use ctx *)
"normalize_match' _ (common_primitive.Src_OS _) = Unknown" |
"normalize_match' _ (common_primitive.Src_Ports opspec) = (intermediate_primitive.Src_Ports (normalize_ports' opspec))" |
"normalize_match' _ (common_primitive.Dst_Ports opspec) = (intermediate_primitive.Dst_Ports (normalize_ports' opspec))" |
"normalize_match' _ (common_primitive.Address_Family Inet) = Unknown" | (* TODO True *)
"normalize_match' _ (common_primitive.Address_Family Inet6) = Unknown" |  (* TODO False *)
(* (intermediate_primitive.IIface ''+'') for (Direction In) doesn't work:
  ''+'' also matches empty string :(
  would need wildcard for non_empty string

but access_matrix only defined for firewall without interfaces anyway \<rightarrow> expand to Address based on ctx
*)
"normalize_match' _ (common_primitive.Direction In) = Unknown" | (* TODO use ctx *)
"normalize_match' _ (common_primitive.Direction Out) = Unknown" | (* TODO use ctx *)
"normalize_match' ctx (common_primitive.Interface (InterfaceGroup g)) = Unknown" | (* TODO use ctx *)
"normalize_match' _ (common_primitive.Interface (InterfaceName i)) = Unknown" |  (* TODO use ctx *)
"normalize_match' _ (common_primitive.Protocol p) = (intermediate_primitive.Protocol p)" |
"normalize_match' _ (common_primitive.L4_Flags _) = Unknown" |
"normalize_match' _ (common_primitive.Extra _) = Unknown"

fun normalize_match :: "common_primitive match_expr \<Rightarrow> 'i intermediate_primitive match_expr" where
"normalize_match MatchAny = MatchAny" |
"normalize_match (MatchNot m) = (MatchNot (normalize_match m))" |
"normalize_match (MatchAnd m1 m2) = (MatchAnd (normalize_match m1) (normalize_match m2))" |
"normalize_match (Match m) = (MatchAny)"

end