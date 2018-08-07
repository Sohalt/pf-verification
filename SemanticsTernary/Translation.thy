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
"normalize_ports (Match (common_primitive.Dst_Ports p)) = match_or (map (\<lambda>(l,u). (common_primitive.Dst_Ports (Binary (RangeIncl l u)))) (wi2l (normalize_ports' p)))" |
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
         (map (\<lambda>(l, u). Src_Ports (Binary (RangeIncl l u))) l)))) =
 Some ((p_sport p) \<in> (\<Union>x\<in>set l. wordinterval_to_set (l2wi l)))"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case sorry
(*  proof(cases "(common_matcher ctx) (case a of (l, u) \<Rightarrow> Src_Ports (Binary (RangeIncl l u))) p")
    case TernaryTrue
    fix lower upper assume uiae:"a = (lower, upper)"
    show ?case
      apply (simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple) sorry
  next
    case TernaryFalse
    then show ?thesis sorry
  next
    case TernaryUnknown
    then show ?thesis sorry
  qed
*)
qed

lemma dst_ports_disjunction_helper:
"ternary_to_bool 
(ternary_ternary_eval
     (map_match_tac (common_matcher ctx) p
       (match_or
         (map (\<lambda>(l, u). Dst_Ports (Binary (RangeIncl l u))) l)))) =
 Some ((p_dport p) \<in> (\<Union>x\<in>set l. wordinterval_to_set (l2wi l)))"
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case sorry
qed


lemma normalize_ports_ok':
"ternary_ternary_eval (map_match_tac (common_matcher ctx) packet m) =
 ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports m))"
proof(induction m rule:normalize_ports.induct)
(*fix p have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (match_expr.Match (Src_Ports p)))) =
            ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports (match_expr.Match (Src_Ports p)))))"
(is "ternary_to_bool ?a = ternary_to_bool ?b")
    apply (simp add:normalize_ports' MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                    ternary_to_bool_bool_to_ternary src_ports_disjunction_helper l2wi_wi2l)
    using l2wi_wi2l by force
  then have src:"?a = ?b" using ternary_to_bool_eq by auto
fix p have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (match_expr.Match (Dst_Ports p)))) =
            ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports (match_expr.Match (Dst_Ports p)))))"
(is "ternary_to_bool ?a = ternary_to_bool ?b")
    apply (simp add:normalize_ports' MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                    ternary_to_bool_bool_to_ternary dst_ports_disjunction_helper l2wi_wi2l)
    using l2wi_wi2l by force
  then have dst:"?a = ?b" using ternary_to_bool_eq by auto
*)
  case (1 p)
  have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (match_expr.Match (Src_Ports p)))) =
        ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports (match_expr.Match (Src_Ports p)))))"
    apply (simp add:normalize_ports' MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                    ternary_to_bool_bool_to_ternary src_ports_disjunction_helper l2wi_wi2l)
    using l2wi_wi2l by force
  then show ?case using ternary_to_bool_eq by auto
next
  case (2 p)
  have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (match_expr.Match (Dst_Ports p)))) =
        ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) packet (normalize_ports (match_expr.Match (Dst_Ports p)))))"
    apply (simp add:normalize_ports' MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple
                    ternary_to_bool_bool_to_ternary dst_ports_disjunction_helper l2wi_wi2l)
    using l2wi_wi2l by force
  then show ?case using ternary_to_bool_eq by auto
next
  case (3 m)
  then show ?case by simp
next
  case (4 m1 m2)
  then show ?case by simp
next
  case ("5_1" va)
  then show ?case by simp
next
case ("5_2" va)
  then show ?case by simp
next
  case ("5_3" va)
then show ?case by simp
next
  case ("5_4" va vb)
  then show ?case by simp
next
  case ("5_5" va)
  then show ?case by simp
next
  case ("5_6" va)
  then show ?case by simp
next
case ("5_7" va)
  then show ?case by simp
next
  case ("5_8" va)
  then show ?case by simp
next
  case "5_9"
  then show ?case by simp
qed


lemma normalize_ports_ok : "matches (common_matcher ctx, \<alpha>) m a d p \<longleftrightarrow> matches (common_matcher ctx, \<alpha>) (normalize_ports m) a d p"
  apply(simp add:matches_def) using normalize_ports_ok' by auto

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

lemma common_matcher_Src_IPv6_TernaryFalse[simp]: "ternary_ternary_eval (map_match_tac (common_matcher ctx) p 
(match_or (map (\<lambda>a. Src (Hostspec (Address (IPv6 a)))) l))) = TernaryFalse"
  by (induction l;simp add:matches_def MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple(1))

lemma common_matcher_Dst_IPv6_TernaryFalse[simp]: "ternary_ternary_eval (map_match_tac (common_matcher ctx) p 
(match_or (map (\<lambda>a. Dst (Address (IPv6 a))) l))) = TernaryFalse"
  by (induction l;simp add:matches_def MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple(1))

fun good_match_expr :: "pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> bool" where
"good_match_expr _ MatchAny = True" |
"good_match_expr ctx (MatchNot m) = good_match_expr ctx m" |
"good_match_expr ctx (MatchAnd m1 m2)= (good_match_expr ctx m1 \<and> good_match_expr ctx m2)" |
"good_match_expr ctx (Match p) = good_primitive ctx p"


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
  proof(cases "p_src p \<in> prefix_to_wordset a")
    case True
    then show ?thesis using Cons(2)
      by(simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple prefix_match_semantics_wordset)
  next
    case False
    then show ?thesis using Cons
      by(simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple prefix_match_semantics_wordset)
  qed
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
  proof(cases "p_dst p \<in> prefix_to_wordset a")
    case True
    then show ?thesis using Cons(2)
      by(simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple prefix_match_semantics_wordset)
  next
    case False
    then show ?thesis using Cons
      by(simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple prefix_match_semantics_wordset)
  qed
qed


lemma remove_tables_ok' :
  assumes "good_match_expr ctx m"
  shows "ternary_ternary_eval (map_match_tac (common_matcher ctx) p m) =
         ternary_ternary_eval (map_match_tac (common_matcher ctx) p (remove_tables ctx m))"
  using assms
proof(induction m rule:remove_tables.induct)
  case (1 ctx name)
  then have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (match_expr.Match (Src (Hostspec (Table name)))))) =
             ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (remove_tables ctx (match_expr.Match (Src (Hostspec (Table name)))))))"
    by (simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple ternary_to_bool_bool_to_ternary
                 src_addr_disjunction_helper[of "wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name))" _ _]
                 match_table_v4_wordinterval
                 wordinterval_CIDR_split_prefixmatch_all_valid_Ball wordinterval_CIDR_split_prefixmatch)
  then show ?case using ternary_to_bool_eq by auto
next
  case (2 ctx name)
  then have "ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (match_expr.Match (Dst (Table name))))) =
             ternary_to_bool (ternary_ternary_eval (map_match_tac (common_matcher ctx) p (remove_tables ctx (match_expr.Match (Dst (Table name))))))"
    by (simp add:MatchOr_def eval_ternary_idempotence_Not eval_ternary_simps_simple ternary_to_bool_bool_to_ternary
                 dst_addr_disjunction_helper[of "wordinterval_CIDR_split_prefixmatch (table_to_wordinterval_v4 (lookup_table ctx name))" _ _]
                 match_table_v4_wordinterval
                 wordinterval_CIDR_split_prefixmatch_all_valid_Ball wordinterval_CIDR_split_prefixmatch)
  then show ?case using ternary_to_bool_eq by auto
next
  case (3 ctx m)
  then show ?case by simp
next
  case (4 ctx m1 m2)
  then show ?case by simp
next
  case ("5_1" ctx)
  then show ?case by simp
next
  case ("5_2" ctx)
  then show ?case by simp
next
  case ("5_3" ctx vc)
  then show ?case by simp
next
  case ("5_4" ctx vc)
  then show ?case by simp
next
  case ("5_5" ctx)
  then show ?case by simp
next
  case ("5_6" ctx va)
  then show ?case by simp
next
  case ("5_7" ctx)
  then show ?case by simp
next
case ("5_8" ctx)
  then show ?case by simp
next
  case ("5_9" ctx v)
  then show ?case by simp
next
case ("5_10" ctx v)
  then show ?case by simp
next
case ("5_11" ctx va)
then show ?case by simp
next
  case ("5_12" ctx va)
  then show ?case by simp
next
  case ("5_13" ctx va vb)
then show ?case by simp
next
  case ("5_14" ctx va)
  then show ?case by simp
next
  case ("5_15" ctx va)
  then show ?case by simp
next
  case ("5_16" ctx va)
  then show ?case by simp
next
  case ("5_17" ctx va)
  then show ?case by simp
next
  case ("5_18" ctx)
  then show ?case by simp
qed


lemma remove_tables_ok :
  assumes "good_match_expr ctx m"
  shows "matches (common_matcher ctx, \<alpha>) m a d p \<longleftrightarrow> matches (common_matcher ctx, \<alpha>) (remove_tables ctx m) a d p"
  using assms by (simp add:matches_def remove_tables_ok')

fun all_match :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr  \<Rightarrow> bool" where
"all_match _ MatchAny = True" |
"all_match P (MatchNot m) = all_match P m" |
"all_match P (MatchAnd m1 m2) = (all_match P m1 \<and> all_match P m2)" |
"all_match P (Match m) = P m"
end