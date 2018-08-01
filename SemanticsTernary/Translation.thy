theory Translation
imports
  "../Firewall_Common"
  "../PrimitiveMatchers"
  Intermediate_Representation
  Matching_Ternary
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

lemma normalize_ports' :
"match_port spec p \<longleftrightarrow> wordinterval_element p (normalize_ports' spec)"
  unfolding match_port_def using linorder_not_less
  by (induction spec rule: normalize_ports'.induct) (auto simp add: inc_le word_Suc_le minus_one_helper3 minus_one_helper5)

fun normalize_match' :: "pfcontext \<Rightarrow> common_primitive \<Rightarrow> 32 intermediate_primitive match_expr" where
"normalize_match' _ (common_primitive.Src UrpfFailed) = (Match Unknown)" |
"normalize_match' _ (common_primitive.Src (Hostspec (Address (IPv4 a)))) = (Match (intermediate_primitive.Src (prefix_to_wordinterval a)))" |
"normalize_match' _ (common_primitive.Src (Hostspec (Address (IPv6 a)))) = MatchNone" |
"normalize_match' ctx (common_primitive.Src (Hostspec (Table t))) = (Match (intermediate_primitive.Src (table_to_wordinterval_v4 (lookup_table ctx t))))" |
"normalize_match' _ (common_primitive.Src (Hostspec AnyHost)) = (Match (intermediate_primitive.Src wordinterval_UNIV))" |
"normalize_match' ctx (common_primitive.Src (Hostspec NoRoute)) = (Match Unknown)" | (* TODO use ctx *)
"normalize_match' ctx (common_primitive.Src (Hostspec (Route r))) = (Match Unknown)" | (* TODO use ctx *)
"normalize_match' _ (common_primitive.Dst (Address (IPv4 a))) = (Match (intermediate_primitive.Dst (prefix_to_wordinterval a)))" |
"normalize_match' _ (common_primitive.Dst (Address (IPv6 a))) = MatchNone" |
"normalize_match' ctx (common_primitive.Dst (Table t)) = (Match (intermediate_primitive.Dst (table_to_wordinterval_v4 (lookup_table ctx t))))" |
"normalize_match' _ (common_primitive.Dst AnyHost) = (Match (intermediate_primitive.Dst wordinterval_UNIV))" |
"normalize_match' ctx (common_primitive.Dst NoRoute) = (Match Unknown)" | (* TODO use ctx *)
"normalize_match' ctx (common_primitive.Dst (Route r)) = (Match Unknown)" | (* TODO use ctx *)
"normalize_match' _ (common_primitive.Src_OS _) = (Match Unknown)" |
"normalize_match' _ (common_primitive.Src_Ports opspec) = (Match (intermediate_primitive.Src_Ports (normalize_ports' opspec)))" |
"normalize_match' _ (common_primitive.Dst_Ports opspec) = (Match (intermediate_primitive.Dst_Ports (normalize_ports' opspec)))" |
"normalize_match' _ (common_primitive.Address_Family Inet) = MatchAny" |
"normalize_match' _ (common_primitive.Address_Family Inet6) = MatchNone" |
"normalize_match' ctx (common_primitive.Interface (Some (InterfaceGroup g)) _) = (Match Unknown)" | (* TODO use ctx *)
"normalize_match' _ (common_primitive.Interface (Some (InterfaceName i)) (Some In)) = (Match (IIface (Iface i)))" |
"normalize_match' _ (common_primitive.Interface (Some (InterfaceName i)) (Some Out)) = (Match (OIface (Iface i)))" |
"normalize_match' _ (common_primitive.Interface (Some (InterfaceName i)) None) = (MatchOr (Match (IIface (Iface i))) (Match (OIface (Iface i))))" |
"normalize_match' _ (common_primitive.Interface None (Some In)) = (Match (IIface IfaceWildcard))" |
"normalize_match' _ (common_primitive.Interface None (Some Out)) = (Match (OIface IfaceWildcard))" |
"normalize_match' _ (common_primitive.Interface None None) = MatchNone" |
"normalize_match' _ (common_primitive.Protocol p) = (Match (intermediate_primitive.Protocol p))" |
"normalize_match' _ (common_primitive.L4_Flags _) = (Match Unknown)" |
"normalize_match' _ (common_primitive.Extra _) = (Match Unknown)"


lemma normalize_match' :
  assumes "good_primitive ctx cp"
  shows "matches (common_matcher ctx, d) (Match cp) a (p::32 simple_packet) = matches (intermediate_matcher, d) (normalize_match' ctx cp) a p"
  unfolding matches_def using assms
proof(induction cp rule:normalize_match'.induct)
case (1 uu)
  then show ?case by simp
next
  case (2 uv a)
  then show ?case by (simp add:prefix_match_semantics_wordset)
next
  case (3 uw a)
  then show ?case by (simp add:MatchNone_def)
next
  case (4 ctx t)
  then show ?case by (simp add:match_table_v4_wordinterval)
next
  case (5 ux)
  then show ?case by simp
next
  case (6 ctx)
  then show ?case by simp
next
  case (7 ctx r)
  then show ?case by simp
next
  case (8 uy a)
  then show ?case by (simp add:prefix_match_semantics_wordset)
next
  case (9 uz a)
then show ?case by (simp add:MatchNone_def)
next
  case (10 ctx t)
  then show ?case by (simp add:match_table_v4_wordinterval)
next
  case (11 va)
  then show ?case by simp
next
  case (12 ctx)
then show ?case by simp
next
  case (13 ctx r)
  then show ?case by simp
next
  case (14 vb vc)
  then show ?case by simp
next
  case (15 vd opspec)
  then show ?case by (simp add:normalize_ports')
next
  case (16 ve opspec)
  then show ?case by (simp add:normalize_ports')
next
  case (17 vf)
  then show ?case by simp
next
  case (18 vg)
  then show ?case by (simp add:MatchNone_def)
next
  case (19 ctx g vh)
  then show ?case by simp
next
  case (20 vi i)
  then show ?case by simp
next
  case (21 vj i)
  then show ?case by simp
next
  case (22 vk i)
  then show ?case by (cases "p_iiface p = i";cases "p_oiface p = i";simp add:MatchOr_def)
next
  case (23 vl)
  then show ?case by simp
next
  case (24 vm)
  then show ?case by simp
next
  case (25 vn)
  then show ?case by (simp add:MatchNone_def)
next
  case (26 vo p)
  then show ?case by simp
next
  case (27 vp vq)
  then show ?case sorry (* FIXME *)
next
  case (28 vr vs)
  then show ?case by simp
qed

fun normalize_match :: "pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> 32 intermediate_primitive match_expr" where
"normalize_match ctx MatchAny = MatchAny" |
"normalize_match ctx (MatchNot m) = (MatchNot (normalize_match ctx m))" |
"normalize_match ctx (MatchAnd m1 m2) = (MatchAnd (normalize_match ctx m1) (normalize_match ctx m2))" |
"normalize_match ctx (Match m) = normalize_match' ctx m"

fun good_match_expr :: "pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> bool" where
"good_match_expr _ MatchAny = True" |
"good_match_expr ctx (MatchNot m) = good_match_expr ctx m" |
"good_match_expr ctx (MatchAnd m1 m2)= (good_match_expr ctx m1 \<and> good_match_expr ctx m2)" |
"good_match_expr ctx (Match p) = good_primitive ctx p"

fun all_match :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr  \<Rightarrow> bool" where
"all_match _ MatchAny = True" |
"all_match P (MatchNot m) = all_match P m" |
"all_match P (MatchAnd m1 m2) = (all_match P m1 \<and> all_match P m2)" |
"all_match P (Match m) = P m"

definition no_unknowns ::"'i intermediate_primitive match_expr \<Rightarrow> bool" where
"no_unknowns m \<longleftrightarrow> all_match (\<lambda>m. m \<noteq> Unknown) m"

fun upper_closure_matchexpr :: "action \<Rightarrow> 32 intermediate_primitive match_expr \<Rightarrow> 32 intermediate_primitive match_expr" where
"upper_closure_matchexpr a (MatchAnd m1 m2) = (MatchAnd (upper_closure_matchexpr a m1) (upper_closure_matchexpr a m2))" |
"upper_closure_matchexpr a (MatchNot m) = (MatchNot (upper_closure_matchexpr a m))" |
"upper_closure_matchexpr Pass (Match Unknown) = MatchAny" |
"upper_closure_matchexpr Block (Match Unknown) = MatchNone" |
"upper_closure_matchexpr _ m = m"

lemma upper_closure_no_unknowns:
  assumes "a = Pass \<or> a = Block"
  shows "no_unknowns (upper_closure_matchexpr a m)"
  using assms unfolding no_unknowns_def by (cases a;induction m rule:upper_closure_matchexpr.induct; auto simp add: MatchNone_def)

fun lower_closure_matchexpr :: "action \<Rightarrow> 32 intermediate_primitive match_expr \<Rightarrow> 32 intermediate_primitive match_expr" where
"lower_closure_matchexpr a (MatchAnd m1 m2) = (MatchAnd (lower_closure_matchexpr a m1) (lower_closure_matchexpr a m2))" |
"lower_closure_matchexpr a (MatchNot m) = (MatchNot (lower_closure_matchexpr a m))" |
"lower_closure_matchexpr Pass (Match Unknown) = MatchNone" |
"lower_closure_matchexpr Block (Match Unknown) = MatchAny" |
"lower_closure_matchexpr _ m = m"

lemma lower_closure_no_unknowns:
  assumes "a = Pass \<or> a = Block"
  shows "no_unknowns (lower_closure_matchexpr a m)"
  using assms unfolding no_unknowns_def by (cases a;induction m rule:lower_closure_matchexpr.induct; auto simp add: MatchNone_def)

end