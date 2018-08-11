theory pfprefix_Translation
imports
  "../pfprefix_Firewall_Common"
  "../pfprefix_PrimitiveMatchers"
  "../pfprefix_Primitives"
  pfprefix_Matching_Ternary
  IP_Addresses.CIDR_Split
  Iptables_Semantics.Negation_Type
  pfprefix_Negation_Type_Matching
begin

(* normalize matches to representation closest to simple_matcher *)

fun match_or :: "'a list \<Rightarrow> 'a match_expr" where
"match_or [] = MatchNot MatchAny" |
"match_or (x#xs) = MatchOr (Match x) (match_or xs)"

fun all_match :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr  \<Rightarrow> bool" where
"all_match _ MatchAny = True" |
"all_match P (MatchNot m) = all_match P m" |
"all_match P (MatchAnd m1 m2) = (all_match P m1 \<and> all_match P m2)" |
"all_match P (Match m) = P m"

definition no_ipv6 :: "common_primitive match_expr \<Rightarrow> bool" where
"no_ipv6 mexpr =
all_match (\<lambda>m. (case m of
(Src (Hostspec (Address (IPv6 _)))) \<Rightarrow> False
| (Dst (Address (IPv6 _))) \<Rightarrow> False
| _ \<Rightarrow> True)) mexpr"

definition no_af :: "common_primitive match_expr \<Rightarrow> bool" where
"no_af mexpr = all_match (\<lambda>m. (case m of (Address_Family _) \<Rightarrow> False)) mexpr"

definition good_match_expr :: "pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> bool" where
"good_match_expr ctx mexpr = all_match (good_primitive ctx) mexpr"

(* words wrap \<rightarrow> needs explicit check for 0 and max_word *)
value "(WordInterval (max_word + 1) max_word)::16 wordinterval"

fun normalize_ports' :: "16 word opspec \<Rightarrow> 16 wordinterval" where
"normalize_ports' (Unary (Eq p)) = (WordInterval p p)" |
"normalize_ports' (Unary (NEq p)) = wordinterval_setminus wordinterval_UNIV (WordInterval p p)" |
"normalize_ports' (Unary (GtEq p)) = (WordInterval p max_word)" |
"normalize_ports' (Unary (Gt p)) = (if (p = max_word)
                                     then Empty_WordInterval
                                     else (WordInterval (p + 1) max_word))" |
"normalize_ports' (Unary (LtEq p)) = (WordInterval 0 p)" |
"normalize_ports' (Unary (Lt p)) = (if (p = 0)
                                     then Empty_WordInterval
                                     else (WordInterval 0 (p - 1)))" |
"normalize_ports' (Binary (RangeIncl from to)) = (WordInterval from to)" |
"normalize_ports' (Binary (RangeExcl from to)) = (if (from = max_word \<or> to = 0) 
                                                   then Empty_WordInterval
                                                   else (WordInterval (from + 1) (to -1)))" |
"normalize_ports' (Binary (RangeComp from to)) = wordinterval_setminus wordinterval_UNIV (WordInterval from to)"

lemma normalize_ports' :
"match_port spec p \<longleftrightarrow> wordinterval_element p (normalize_ports' spec)"
  unfolding match_port_def using linorder_not_less
  by (induction spec rule: normalize_ports'.induct)
     (auto simp add: inc_le word_Suc_le minus_one_helper3 minus_one_helper5)

fun normalize_ports :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"normalize_ports (Match (common_primitive.Src_Ports (L4Ports proto p))) =
 match_or (map (\<lambda>(l,u). (common_primitive.Src_Ports (L4Ports proto (Binary (RangeIncl l u)))))
            (wi2l (normalize_ports' p)))" |
"normalize_ports (Match (common_primitive.Dst_Ports (L4Ports proto p))) =
 match_or (map (\<lambda>(l,u). (common_primitive.Dst_Ports (L4Ports proto (Binary (RangeIncl l u)))))
            (wi2l (normalize_ports' p)))" |
"normalize_ports (MatchNot m) = (MatchNot (normalize_ports m))" |
"normalize_ports (MatchAnd m1 m2) = (MatchAnd (normalize_ports m1) (normalize_ports m2))" |
"normalize_ports m = m"


lemma ternary_to_bool_eq:
  assumes "ternary_to_bool e1 = ternary_to_bool e2"
  shows "e1 = e2"
  using assms by(cases e1;cases e2;auto)

lemma src_ports_disjunction_helper:
"ternary_to_bool
(ternary_ternary_eval
     (map_match_tac (common_matcher ctx) p
       (match_or
         (map (\<lambda>(l, u). Src_Ports (L4Ports proto (Binary (RangeIncl l u)))) l)))) =
 Some (proto = (p_proto p) \<and>(p_sport p) \<in> (\<Union>x\<in>set l. wordinterval_to_set (l2wi l)))"
proof(induction l rule: l2wi.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case
    by (auto simp add:MatchOr_def eval_ternary_idempotence_Not
                      eval_ternary_simps_simple match_port_def ternary_to_bool_bool_to_ternary)
next
  case (3 l u)
  then show ?case
    by (cases "(proto = p_proto p) \<and> (l \<le> p_sport p \<and> p_sport p \<le> u)")
       (auto simp add: eval_ternary_idempotence_Not MatchOr_def
                       eval_ternary_simps_simple match_port_def ternary_to_bool_bool_to_ternary)
qed

lemma dst_ports_disjunction_helper:
"ternary_to_bool
(ternary_ternary_eval
     (map_match_tac (common_matcher ctx) p
       (match_or
         (map (\<lambda>(l, u). Dst_Ports (L4Ports proto (Binary (RangeIncl l u)))) l)))) =
 Some ((proto = p_proto p) \<and> (p_dport p) \<in> (\<Union>x\<in>set l. wordinterval_to_set (l2wi l)))"
proof(induction l rule: l2wi.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case
    by (auto simp add:MatchOr_def eval_ternary_idempotence_Not
                      eval_ternary_simps_simple match_port_def ternary_to_bool_bool_to_ternary)
next
  case (3 l u)
  then show ?case
    by (cases "(proto = p_proto p) \<and> (l \<le> p_dport p \<and> p_dport p \<le> u)")
       (auto simp add: eval_ternary_idempotence_Not MatchOr_def
                       eval_ternary_simps_simple match_port_def ternary_to_bool_bool_to_ternary)
qed

lemma normalize_ports_preserves_semantics':
"ternary_ternary_eval (map_match_tac (common_matcher ctx) packet m) =
 ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports m))"
proof(induction m rule:normalize_ports.induct)
  case (1 proto p)
  have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (match_expr.Match (Src_Ports (L4Ports proto p))))) =
        ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports (match_expr.Match (Src_Ports (L4Ports proto p))))))"
    apply (simp add:normalize_ports' MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                    ternary_to_bool_bool_to_ternary src_ports_disjunction_helper l2wi_wi2l)
    using l2wi_wi2l by force
  then show ?case using ternary_to_bool_eq by auto
next
  case (2 proto p)
  have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (match_expr.Match (Dst_Ports (L4Ports proto p))))) =
        ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports (match_expr.Match (Dst_Ports (L4Ports proto p))))))"
    apply (simp add:normalize_ports' MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                    ternary_to_bool_bool_to_ternary dst_ports_disjunction_helper l2wi_wi2l)
    using l2wi_wi2l by force
  then show ?case using ternary_to_bool_eq by auto
qed simp+

lemma normalize_ports_preserves_semantics:
 "matches (common_matcher ctx, \<alpha>) m a d p \<longleftrightarrow> matches (common_matcher ctx, \<alpha>) (normalize_ports m) a d p"
  apply(simp add:matches_def) using normalize_ports_preserves_semantics' by auto

definition normalized_ports :: "common_primitive match_expr \<Rightarrow> bool" where
"normalized_ports mexpr =
all_match
(\<lambda>m. (case m of
(Src_Ports (L4Ports _ (Binary bop))) \<Rightarrow> is_RangeIncl bop
| (Src_Ports (L4Ports _ (Unary _))) \<Rightarrow> False
| (Dst_Ports (L4Ports _ (Binary bop))) \<Rightarrow> is_RangeIncl bop
| (Dst_Ports (L4Ports _ (Unary _))) \<Rightarrow> False
| _ \<Rightarrow> True))
mexpr"

(* FIXME remove after Isabelle2018 *)
lemma [simp]: "wi2l Empty_WordInterval = []"
  unfolding Empty_WordInterval_def
  by simp

lemma [simp]:
  "normalized_ports
          (match_or (map (\<lambda>(l, u). Src_Ports (L4Ports proto (Binary (RangeIncl l u)))) xs))"
  by (induction xs) (auto simp: MatchOr_def normalized_ports_def)

lemma [simp]:
  "normalized_ports
          (match_or (map (\<lambda>(l, u). Dst_Ports (L4Ports proto (Binary (RangeIncl l u)))) xs))"
  by (induction xs) (auto simp: MatchOr_def normalized_ports_def)

lemma normalize_ports_ok:
  "normalized_ports (normalize_ports m)"
by (induction m rule:normalize_ports.induct)
   ((simp add:normalized_ports_def; fail) | simp)+


fun remove_tables ::"pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"remove_tables ctx (Match (common_primitive.Src (Hostspec (Table name)))) = 
  (MatchOr
    (match_or (map (\<lambda> a. (common_primitive.Src (Hostspec (Address (IPv4 a)))))
                (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))
    (match_or (map (\<lambda> a. (common_primitive.Src (Hostspec (Address (IPv6 a)))))
                (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name))))))" |
"remove_tables ctx (Match (common_primitive.Dst (Table name))) =
  (MatchOr
    (match_or (map (\<lambda> a. (common_primitive.Dst (Address (IPv4 a))))
                (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))
    (match_or (map (\<lambda> a. (common_primitive.Dst (Address (IPv6 a))))
                (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name))))))" |
"remove_tables ctx (MatchNot m) = (MatchNot (remove_tables ctx m))" |
"remove_tables ctx (MatchAnd m1 m2) = (MatchAnd (remove_tables ctx m1) (remove_tables ctx m2))" |
"remove_tables ctx m = m"

lemma common_matcher_Src_IPv6_TernaryFalse[simp]:
"ternary_ternary_eval (map_match_tac (common_matcher ctx) p
(match_or (map (\<lambda>a. Src (Hostspec (Address (IPv6 a)))) l))) = TernaryFalse"
  by (induction l)
     (simp add:matches_def MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple(1))+

lemma common_matcher_Dst_IPv6_TernaryFalse[simp]:
"ternary_ternary_eval (map_match_tac (common_matcher ctx) p
(match_or (map (\<lambda>a. Dst (Address (IPv6 a))) l))) = TernaryFalse"
  by (induction l)
     (simp add:matches_def MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple(1))+


lemma src_addr_disjunction_helper:
  assumes "\<forall> x\<in>set l. valid_prefix x"
  shows "ternary_to_bool
(ternary_ternary_eval
     (map_match_tac (common_matcher ctx) p
       (match_or
         (map (\<lambda>a. Src (Hostspec (Address (IPv4 a)))) l)))) =
 Some ((p_src p) \<in> (\<Union>x\<in>set l. prefix_to_wordset x))"
  using assms
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by (cases "p_src p \<in> prefix_to_wordset a")
       (simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                 prefix_match_semantics_wordset)+
qed

lemma dst_addr_disjunction_helper:
  assumes "\<forall> x\<in>set l. valid_prefix x"
  shows "ternary_to_bool
(ternary_ternary_eval
     (map_match_tac (common_matcher ctx) p
       (match_or
         (map (\<lambda>a. Dst (Address (IPv4 a))) l)))) =
 Some ((p_dst p) \<in> (\<Union>x\<in>set l. prefix_to_wordset x))"
  using assms
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by (cases "p_dst p \<in> prefix_to_wordset a")
       (simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                 prefix_match_semantics_wordset)+
qed


lemma remove_tables_preserves_semantics' :
  assumes "good_match_expr ctx m"
  shows "ternary_ternary_eval (map_match_tac (common_matcher ctx) p m) =
         ternary_ternary_eval (map_match_tac (common_matcher ctx) p (remove_tables ctx m))"
  using assms
proof(induction m rule:remove_tables.induct)
  case (1 ctx name)
  then have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (match_expr.Match (Src (Hostspec (Table name)))))) =
             ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (remove_tables ctx (match_expr.Match (Src (Hostspec (Table name)))))))"
    by (simp add:good_match_expr_def MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple ternary_to_bool_bool_to_ternary
                 src_addr_disjunction_helper[of "wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name))" _ _]
                 match_table_v4_wordinterval
                 wordinterval_CIDR_split_prefixmatch_all_valid_Ball wordinterval_CIDR_split_prefixmatch)
  then show ?case using ternary_to_bool_eq by auto
next
  case (2 ctx name)
  then have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (match_expr.Match (Dst (Table name))))) =
             ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (remove_tables ctx (match_expr.Match (Dst (Table name))))))"
    by (simp add:good_match_expr_def MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple ternary_to_bool_bool_to_ternary
                 dst_addr_disjunction_helper[of "wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name))" _ _]
                 match_table_v4_wordinterval
                 wordinterval_CIDR_split_prefixmatch_all_valid_Ball wordinterval_CIDR_split_prefixmatch)
  then show ?case using ternary_to_bool_eq by auto
qed (simp add:good_match_expr_def)+


lemma remove_tables_preserves_semantics :
  assumes "good_match_expr ctx m"
    shows "matches (common_matcher ctx, \<alpha>) m a d p \<longleftrightarrow> matches (common_matcher ctx, \<alpha>) (remove_tables ctx m) a d p"
  using assms by (simp add:good_match_expr_def matches_def remove_tables_preserves_semantics')

definition no_tables :: "common_primitive match_expr \<Rightarrow> bool" where
"no_tables mexpr = all_match
(\<lambda>m. (case m of
(Src (Hostspec (Table _))) \<Rightarrow> False
|(Dst (Table _)) \<Rightarrow> False
| _ \<Rightarrow> True))
mexpr"

lemma [simp]:
  "no_tables
          (match_or (map (\<lambda>a. Src (Hostspec (Address (IPv4 a)))) xs))"
  by (induction xs) (auto simp: MatchOr_def no_tables_def)

lemma [simp]:
  "no_tables
          (match_or (map (\<lambda>a. Src (Hostspec (Address (IPv6 a)))) xs))"
  by (induction xs) (auto simp: MatchOr_def no_tables_def)

lemma [simp]:
  "no_tables
          (match_or (map (\<lambda>a. Dst (Address (IPv4 a))) xs))"
  by (induction xs) (auto simp: MatchOr_def no_tables_def)

lemma [simp]:
  "no_tables
          (match_or (map (\<lambda>a. Dst (Address (IPv6 a))) xs))"
  by (induction xs) (auto simp: MatchOr_def no_tables_def)

lemma remove_tables_ok:
  "(no_tables (remove_tables ctx m))"
proof(induction ctx m rule:remove_tables.induct)
  case (1 ctx name)
  then have "no_tables (match_or
         (map (\<lambda>a. Src (Hostspec (Address (IPv4 a))))
           (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))" by simp
  moreover have "no_tables (match_or
         (map (\<lambda>a. Src (Hostspec (Address (IPv6 a))))
           (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name)))))" by simp
  ultimately show ?case by (simp add:MatchOr_def no_tables_def)
next
  case (2 ctx name)
  then have "no_tables (match_or
         (map (\<lambda>a. Dst (Address (IPv4 a)))
           (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))" by simp
  moreover have "no_tables (match_or
         (map (\<lambda>a. Dst (Address (IPv6 a)))
           (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name)))))" by simp
  ultimately show ?case by (simp add:MatchOr_def no_tables_def)
qed (simp add:no_tables_def)+

end