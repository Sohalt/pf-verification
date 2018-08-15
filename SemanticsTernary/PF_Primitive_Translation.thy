theory PF_Primitive_Translation
imports
  "../PF_Firewall_Common"
  "../PF_PrimitiveMatchers"
  "../PF_Primitives"
  PF_Matching_Ternary
  IP_Addresses.CIDR_Split
  Iptables_Semantics.Negation_Type
  PF_Negation_Type_Matching
  PF_Predicates
  "../PF_Foo"
begin

(* normalize matches to representation closest to simple_matcher *)

fun match_or :: "'a list \<Rightarrow> 'a match_expr" where
"match_or [] = MatchNot MatchAny" |
"match_or (x#xs) = MatchOr (Match x) (match_or xs)"

(* -------------- Ports -------------- *)

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
"normalize_ports' (Binary (RangeExcl from to)) = 
  (if (from = max_word \<or> to = 0)
    then Empty_WordInterval
    else (WordInterval (from + 1) (to -1)))" |
"normalize_ports' (Binary (RangeComp from to)) =
  wordinterval_setminus wordinterval_UNIV (WordInterval from to)"

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

definition normalize_ports_rs :: "common_primitive ruleset \<Rightarrow> common_primitive ruleset" where
"normalize_ports_rs = optimize_matches normalize_ports"

lemma normalize_ports_rs_preserves_semantics:
  assumes "simple_ruleset rs"
      and "good_matcher (common_matcher ctx,\<alpha>)"
    shows "pf_approx rs (common_matcher ctx,\<alpha>) p =
           pf_approx (normalize_ports_rs rs) (common_matcher ctx,\<alpha>) p"
  unfolding normalize_ports_rs_def
  using optimize_matches_preserves_semantics assms normalize_ports_preserves_semantics
  by metis

lemma src_ports_good_primitive_helper: 
"all_match (good_primitive ctx)
     (match_or
       (map (\<lambda>(l, u). Src_Ports (L4Ports proto (Binary (RangeIncl l u)))) l))"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by(cases a) (auto simp:MatchOr_def)
qed

lemma dst_ports_good_primitive_helper: 
"all_match (good_primitive ctx)
     (match_or
       (map (\<lambda>(l, u). Dst_Ports (L4Ports proto (Binary (RangeIncl l u)))) l))"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by(cases a) (auto simp:MatchOr_def)
qed

lemma normalize_ports_preserves_good_match_expr:
  assumes "good_match_expr ctx m"
  shows "good_match_expr ctx (normalize_ports m)"
  using assms unfolding good_match_expr_def
proof (induction m rule:normalize_ports.induct)
  case (1 proto p)
  then show ?case by (simp add: src_ports_good_primitive_helper)
next
  case (2 proto p)
  then show ?case by (simp add: dst_ports_good_primitive_helper)
qed auto


lemma normalize_ports_rs_preserves_simple_ruleset:
  assumes "simple_ruleset rs"
    shows "simple_ruleset (normalize_ports_rs rs)"
  unfolding normalize_ports_rs_def using assms optimize_matches_simple_ruleset by blast

lemma normalize_ports_rs_preserves_wf_ruleset:
  assumes "simple_ruleset rs"
      and "wf_ruleset ctx rs"
    shows "wf_ruleset ctx (normalize_ports_rs rs)"
proof(-)
  have "all_PfRules_P (\<lambda>r. good_match_expr ctx (normalize_ports (pf_rule.get_match r))) rs"
    using assms proof(induction rs)
    case Nil
    then show ?case by simp
  next
    case (Cons a rs)
    then show ?case by(cases a)
        (auto simp add:normalize_ports_preserves_good_match_expr
                       simple_ruleset_def wf_ruleset_def)
  qed
  then have "all_PfRules_P (\<lambda>r. good_match_expr ctx (pf_rule.get_match r))
                  (normalize_ports_rs rs)" unfolding normalize_ports_rs_def
    using optimize_matches_preserves_all_PfRules_P assms by simp
  then show ?thesis 
    using assms normalize_ports_rs_preserves_simple_ruleset simple_ruleset_wf_ruleset
    by simp
qed

lemma normalize_ports_no_tables_src_helper:
"no_tables
        (match_or
          (map (\<lambda>(l, u). Src_Ports (L4Ports proto (Binary (RangeIncl l u))))
            l))"
  by (induction l) (auto simp:MatchOr_def no_tables_def)

lemma normalize_ports_no_tables_dst_helper:
"no_tables
        (match_or
          (map (\<lambda>(l, u). Dst_Ports (L4Ports proto (Binary (RangeIncl l u))))
            l))"
  by (induction l) (auto simp:MatchOr_def no_tables_def)

lemma normalize_ports_preserves_no_tables:
  assumes "no_tables m"
  shows "no_tables (normalize_ports m)"
  using assms apply (induction m rule:normalize_ports.induct)
  by (auto simp:normalize_ports_no_tables_src_helper
                normalize_ports_no_tables_dst_helper)
     (auto simp:no_tables_def)
                 
lemma normalize_ports_rs_preserves_no_tables_rs:
  assumes "simple_ruleset rs"
      and "no_tables_rs rs"
    shows "no_tables_rs (normalize_ports_rs rs)"
proof(-)
  have "all_PfRules_P (\<lambda>r. (no_tables (normalize_ports (pf_rule.get_match r)))) rs" using assms
  proof(induction rs)
    case Nil
    then show ?case by simp
  next
    case (Cons a rs)
    then show ?case by (cases a)
        (auto simp:normalize_ports_preserves_no_tables 
                   simple_ruleset_def no_tables_rs_def)
  qed
  then have "all_PfRules_P (\<lambda>r. no_tables (pf_rule.get_match r))
                  (normalize_ports_rs rs)" unfolding normalize_ports_rs_def
    using assms optimize_matches_preserves_all_PfRules_P by simp
  then show ?thesis unfolding normalize_ports_rs_def no_tables_rs_def
  using assms normalize_ports_rs_preserves_simple_ruleset simple_ruleset_wf_ruleset
  by simp
qed


(* -------------- Tables -------------- *)

fun remove_tables ::"pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"remove_tables ctx (Match (common_primitive.Src (Hostspec (Table name)))) =
  (MatchOr
    (match_or 
      (map (\<lambda> a. (common_primitive.Src (Hostspec (Address (IPv4 a)))))
        (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))
    (match_or
      (map (\<lambda> a. (common_primitive.Src (Hostspec (Address (IPv6 a)))))
        (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name))))))" |
"remove_tables ctx (Match (common_primitive.Dst (Table name))) =
  (MatchOr
    (match_or
      (map (\<lambda> a. (common_primitive.Dst (Address (IPv4 a))))
        (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))
    (match_or
      (map (\<lambda> a. (common_primitive.Dst (Address (IPv6 a))))
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
  shows "matches (common_matcher ctx, \<alpha>) m a d p \<longleftrightarrow> 
         matches (common_matcher ctx, \<alpha>) (remove_tables ctx m) a d p"
  using assms by (simp add:good_match_expr_def matches_def remove_tables_preserves_semantics')

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

definition remove_tables_rs :: "pfcontext \<Rightarrow> common_primitive ruleset \<Rightarrow> common_primitive ruleset" where
"remove_tables_rs ctx = optimize_matches (remove_tables ctx)"

lemma remove_tables_rs_preserves_semantics:
  assumes "wf_ruleset ctx rs"
      and "simple_ruleset rs"
      and "good_matcher (common_matcher ctx,\<alpha>)"
    shows "pf_approx rs (common_matcher ctx,\<alpha>) p =
           pf_approx (remove_tables_rs ctx rs) (common_matcher ctx,\<alpha>) p"
proof(-)
  have "\<forall>r\<in>set rs.
       case r of PfRule r \<Rightarrow> pf_rule.get_action r \<noteq> ActionMatch \<and> good_match_expr ctx (pf_rule.get_match r)
       | Anchor _ _ \<Rightarrow> True" using assms(1) assms(2) unfolding wf_ruleset_def simple_ruleset_def
    by (simp add: line.case_eq_if)
  have "(\<And>m a d. a \<noteq> ActionMatch \<and> good_match_expr ctx m \<Longrightarrow>
  matches (common_matcher ctx,\<alpha>) (remove_tables ctx m) a d p = matches(common_matcher ctx,\<alpha>) m a d p)"
    using remove_tables_preserves_semantics good_matcher_def assms(3)
    by blast

  show ?thesis unfolding remove_tables_rs_def
    apply (rule optimize_matches_generic[symmetric])
    by fact+
qed

lemma src_ipv4_good_match_expr_helper:
  assumes "\<forall> p \<in> set l. valid_prefix p"
  shows
 "good_match_expr ctx 
   (match_or
     (map (\<lambda>a. Src (Hostspec (Address (IPv4 a))))
       l))"  
  using assms
  by (induction l) (auto simp:good_match_expr_def MatchOr_def)

lemma src_ipv6_good_match_expr_helper:
  assumes "\<forall> p \<in> set l. valid_prefix p"
  shows
 "good_match_expr ctx 
   (match_or
     (map (\<lambda>a. Src (Hostspec (Address (IPv6 a))))
       l))"  
  using assms
  by (induction l) (auto simp:good_match_expr_def MatchOr_def)

lemma dst_ipv4_good_match_expr_helper:
  assumes "\<forall> p \<in> set l. valid_prefix p"
  shows
 "good_match_expr ctx 
   (match_or
     (map (\<lambda>a. Dst (Address (IPv4 a)))
       l))"  
  using assms
  by (induction l) (auto simp:good_match_expr_def MatchOr_def)

lemma dst_ipv6_good_match_expr_helper:
  assumes "\<forall> p \<in> set l. valid_prefix p"
  shows
 "good_match_expr ctx 
   (match_or
     (map (\<lambda>a. Dst (Address (IPv6 a)))
       l))"  
  using assms
  by (induction l) (auto simp:good_match_expr_def MatchOr_def)

lemma remove_tables_preserves_good_match_expr:
  assumes "good_match_expr ctx m"
  shows "good_match_expr ctx (remove_tables ctx m)"
  using assms
proof(induction m rule:remove_tables.induct)
  case (1 ctx name)
  have "good_match_expr ctx
         (match_or
           (map (\<lambda>a. Src (Hostspec (Address (IPv4 a))))
             (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))"
    using src_ipv4_good_match_expr_helper wordinterval_CIDR_split_prefixmatch_all_valid_Ball by blast
  moreover have "good_match_expr ctx
                  (match_or
                    (map (\<lambda>a. Src (Hostspec (Address (IPv6 a))))
                      (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name)))))"
    using src_ipv6_good_match_expr_helper wordinterval_CIDR_split_prefixmatch_all_valid_Ball by blast
  ultimately show ?case by (auto simp:MatchOr_def good_match_expr_def)
next
  case (2 ctx name)
  have "good_match_expr ctx
         (match_or
           (map (\<lambda>a. Dst (Address (IPv4 a)))
             (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name)))))"
    using dst_ipv4_good_match_expr_helper wordinterval_CIDR_split_prefixmatch_all_valid_Ball by blast
  moreover have "good_match_expr ctx
                  (match_or
                    (map (\<lambda>a. Dst (Address (IPv6 a)))
                      (wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v6 (lookup_table ctx name)))))"
    using dst_ipv6_good_match_expr_helper wordinterval_CIDR_split_prefixmatch_all_valid_Ball by blast
  ultimately show ?case by (auto simp:MatchOr_def good_match_expr_def)
qed (auto simp:MatchOr_def good_match_expr_def)


lemma remove_tables_rs_preserves_simple_ruleset:
  assumes "simple_ruleset rs"
    shows "simple_ruleset (remove_tables_rs ctx rs)"
  unfolding remove_tables_rs_def using assms optimize_matches_simple_ruleset by blast

lemma remove_tables_rs_preserves_wf_ruleset:
  assumes "simple_ruleset rs"
      and "wf_ruleset ctx rs"
    shows "wf_ruleset ctx (remove_tables_rs ctx rs)"
proof(-)
  have "all_PfRules_P (\<lambda>r. good_match_expr ctx (remove_tables ctx (pf_rule.get_match r))) rs"
    using assms proof(induction rs)
    case Nil
    then show ?case by simp
  next
    case (Cons a rs)
    then show ?case by(cases a)
        (auto simp add:remove_tables_preserves_good_match_expr
                       simple_ruleset_def wf_ruleset_def)
  qed
  then have "all_PfRules_P (\<lambda>r. good_match_expr ctx (pf_rule.get_match r))
                  (remove_tables_rs ctx rs)" unfolding remove_tables_rs_def
    using optimize_matches_preserves_all_PfRules_P assms by simp
  then show ?thesis 
    using assms remove_tables_rs_preserves_simple_ruleset simple_ruleset_wf_ruleset
    by simp
qed

lemma remove_tables_rs_ok: 
  assumes "simple_ruleset rs"
  shows "no_tables_rs (remove_tables_rs ctx rs)"
  unfolding no_tables_rs_def remove_tables_rs_def
  using optimize_matches_preserves_all_PfRules_P'[where f="remove_tables ctx"]
    assms remove_tables_ok by auto


(* -------------- IPv6 -------------- *)


fun remove_ipv6 :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"remove_ipv6 (Match (Src (Hostspec (Address (IPv6 _))))) = MatchNone" |
"remove_ipv6 (Match (Dst (Address (IPv6 _)))) = MatchNone" |
"remove_ipv6 (Match (Address_Family Inet)) = MatchAny" |
"remove_ipv6 (Match (Address_Family Inet6)) = MatchNone" |
"remove_ipv6 MatchAny = MatchAny" |
"remove_ipv6 (Match m) = (Match m)" |
"remove_ipv6 (MatchNot m) = (MatchNot (remove_ipv6 m))" |
"remove_ipv6 (MatchAnd m1 m2) = (MatchAnd (remove_ipv6 m1) (remove_ipv6 m2))"

definition ipv4_only :: "common_primitive ruleset \<Rightarrow> common_primitive ruleset" where
"ipv4_only = optimize_matches remove_ipv6"

lemma remove_ipv6_preserves_good_match_expr:
  assumes "good_match_expr ctx m"
  shows "good_match_expr ctx (remove_ipv6 m)"
  using assms by (induction m rule:remove_ipv6.induct)
                 (auto simp:good_match_expr_def MatchNone_def)

lemma ipv4_only_preserves_simple_ruleset:
  assumes "simple_ruleset rs"
  shows "simple_ruleset (ipv4_only rs)"
  using assms by (auto simp:ipv4_only_def optimize_matches_simple_ruleset)

lemma ipv4_only_preserves_wf_ruleset:
  assumes "simple_ruleset rs"
      and "wf_ruleset ctx rs"
    shows "wf_ruleset ctx (ipv4_only rs)"
proof(-)
  have "all_PfRules_P (\<lambda>r. good_match_expr ctx (remove_ipv6 (pf_rule.get_match r))) rs"
  using assms proof(induction rs)
    case Nil
    then show ?case by simp
  next
    case (Cons a rs)
    then show ?case by(cases a)
        (auto simp add:remove_ipv6_preserves_good_match_expr
                       simple_ruleset_def wf_ruleset_def)
  qed
  then have "all_PfRules_P (\<lambda>r. good_match_expr ctx (pf_rule.get_match r))
                  (ipv4_only rs)" unfolding ipv4_only_def
    using assms optimize_matches_preserves_all_PfRules_P by simp
  then show ?thesis
  using assms ipv4_only_preserves_simple_ruleset simple_ruleset_wf_ruleset
  by simp
qed

lemma no_ipv6_ok: "no_ipv6 (remove_ipv6 m)"
  by (induction m rule:remove_ipv6.induct) (auto simp: no_ipv6_def MatchNone_def)

lemma no_af_ok: "no_af (remove_ipv6 m)"
  by (induction m rule:remove_ipv6.induct) (auto simp: no_af_def MatchNone_def)

lemma ipv4_only_no_ipv6:
  assumes "simple_ruleset rs"
  shows "no_ipv6_rs (ipv4_only rs)"
  unfolding no_ipv6_rs_def ipv4_only_def
  using optimize_matches_preserves_all_PfRules_P' assms no_ipv6_ok by auto

lemma ipv4_only_no_af:
  assumes "simple_ruleset rs"
  shows "no_af_rs (ipv4_only rs)"
  unfolding no_af_rs_def ipv4_only_def
  using optimize_matches_preserves_all_PfRules_P' assms no_af_ok by auto

(* -------------- AnyHost -------------- *)

fun remove_match_any' ::  "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"remove_match_any' (Match (Src (Hostspec AnyHost))) = MatchAny" |
"remove_match_any' (Match (Dst AnyHost)) = MatchAny" |
"remove_match_any' (Match m) = (Match m)" |
"remove_match_any' MatchAny = MatchAny" |
"remove_match_any' (MatchNot m) = (MatchNot (remove_match_any' m))" |
"remove_match_any' (MatchAnd m1 m2) = (MatchAnd (remove_match_any' m1) (remove_match_any' m2))"

lemma remove_match_any'_ok: "no_anyhost (remove_match_any' m)"
  by (induction m rule:remove_match_any'.induct) (auto simp: no_anyhost_def MatchNone_def)

definition remove_match_any :: "common_primitive ruleset \<Rightarrow> common_primitive ruleset" where
"remove_match_any = optimize_matches remove_match_any'"

lemma remove_match_any_ok:
  assumes "simple_ruleset rs"
  shows "no_anyhost_rs (remove_match_any rs)"
  unfolding no_anyhost_rs_def remove_match_any_def
  using optimize_matches_preserves_all_PfRules_P' assms remove_match_any'_ok by auto

lemma remove_match_any_preserves_simple_ruleset:
  assumes "simple_ruleset rs"
  shows "simple_ruleset (remove_match_any rs)"
  using assms by (auto simp:remove_match_any_def optimize_matches_simple_ruleset)

lemma remove_match_any'_preserves_good_match_expr:
  assumes "good_match_expr ctx m"
  shows "good_match_expr ctx (remove_match_any' m)"
  using assms by (induction m rule:remove_match_any'.induct)
                 (auto simp:good_match_expr_def MatchNone_def)

lemma remove_match_any_preserves_wf_ruleset:
  assumes "simple_ruleset rs"
  and "wf_ruleset ctx rs"
shows "wf_ruleset ctx (remove_match_any rs)"
proof(-)
  have "all_PfRules_P (\<lambda>r. good_match_expr ctx (remove_match_any' (pf_rule.get_match r))) rs"
  using assms proof(induction rs)
    case Nil
    then show ?case by simp
  next
    case (Cons a rs)
    then show ?case by(cases a)
        (auto simp add:remove_match_any'_preserves_good_match_expr
                       simple_ruleset_def wf_ruleset_def)
  qed
  then have "all_PfRules_P (\<lambda>r. good_match_expr ctx (pf_rule.get_match r))
                  (remove_match_any rs)" unfolding remove_match_any_def
    using assms optimize_matches_preserves_all_PfRules_P by simp
  then show ?thesis
  using assms remove_match_any_preserves_simple_ruleset simple_ruleset_wf_ruleset
  by simp
qed

end