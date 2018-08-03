theory Translation
imports
  "../Firewall_Common"
  "../PrimitiveMatchers"
  Matching_Ternary
  IP_Addresses.CIDR_Split
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

fun normalize_ports :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"normalize_ports (Match (common_primitive.Src_Ports p)) = match_or (map (\<lambda>(l,u). (common_primitive.Src_Ports (Binary (RangeIncl l u)))) (wi2l (normalize_ports' p)))" |
"normalize_ports (MatchNot m) = (MatchNot (normalize_ports m))" |
"normalize_ports (MatchAnd m1 m2) = (MatchAnd (normalize_ports m1) (normalize_ports m2))" |
"normalize_ports m = m"

lemma normalize_ports_ok : "matches \<gamma> m a p \<longleftrightarrow> matches \<gamma> (normalize_ports m) a p"
  sorry

fun remove_tables ::"pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"remove_tables ctx (Match (common_primitive.Src (Hostspec (Table name)))) = (MatchOr
(match_or (map (\<lambda> a. (common_primitive.Src (Hostspec (Address (IPv4 a))))) (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))
(match_or (map (\<lambda> a. (common_primitive.Src (Hostspec (Address (IPv6 a))))) (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name))))))" |
"remove_tables ctx (Match (common_primitive.Dst (Table name))) = (MatchOr
(match_or (map (\<lambda> a. (common_primitive.Dst (Address (IPv4 a)))) (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))
(match_or (map (\<lambda> a. (common_primitive.Dst (Address (IPv6 a)))) (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name))))))" |
"remove_tables ctx (MatchNot m) = (MatchNot (remove_tables ctx m))" |
"remove_tables ctx (MatchAnd m1 m2) = (MatchAnd (remove_tables ctx m1) (remove_tables ctx m2))" |
"remove_tables ctx m = m"

lemma remove_table_ok : "matches (common_matcher ctx, \<alpha>) m a p \<longleftrightarrow> matches (common_matcher ctx, \<alpha>) (remove_table ctx m) a p"
  sorry
(*proof(induction m rule:remove_table.induct;simp)*)


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
end