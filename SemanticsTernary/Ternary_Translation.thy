theory Ternary_Translation
  imports "../Pf_To_Simple_Firewall"
          Semantics_Ternary
          Unknown_Match_Tacs
begin

lemma filter_approx_to_pf_approx:
  assumes "\<forall> d. (filter_approx l1 \<gamma> p d = filter_approx l2 \<gamma> p d)"
  shows "pf_approx l1 \<gamma> p = pf_approx l2 \<gamma> p" unfolding pf_approx_def using assms by simp

lemma filter_approx_add_equiv_prefix :
  assumes "filter_approx l1 \<gamma> p d = filter_approx l2 \<gamma> p d"
          "\<And>d. filter_approx l3 \<gamma> p d = filter_approx l4 \<gamma> p d"
  shows "filter_approx (l1@l3) \<gamma> p d = filter_approx (l2@l4) \<gamma> p d"
proof -
    have "filter_approx (l1@l3) \<gamma> p d = filter_approx l3 \<gamma> p (filter_approx l1 \<gamma> p d)" by (simp add: filter_approx_chain)
    moreover have "filter_approx (l2@l4) \<gamma> p d = filter_approx l4 \<gamma> p (filter_approx l2 \<gamma> p d)" by (simp add: filter_approx_chain)
    ultimately show ?thesis using assms by auto
  qed

lemma filter_approx_add_same_prefix :
  assumes "\<And>d. filter_approx l1 \<gamma> p d = filter_approx l2 \<gamma> p d"
  shows "filter_approx (l@l1) \<gamma> p d = filter_approx (l@l2) \<gamma> p d"
  by (metis assms filter_approx_add_equiv_prefix)

lemma and_each_false[simp]:
  assumes "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m)) = TernaryFalse"
  shows "filter_approx (and_each m l) \<gamma> p d = d"
proof(cases d)
  case (Final x1)
  then show ?thesis by simp
next
  case (Preliminary x2)
  then show ?thesis
  proof(induction l)
    case Nil
    then show ?case by (cases d, auto)
  next
    case (Cons a l)
    then show ?case
    proof(cases a)
      case (PfRule x1)
      then show ?thesis using Cons unfolding PfRule using assms apply simp unfolding matches_def
        by (simp add: eval_ternary_simps_simple(3))
    next
      case (Anchor x21 x22)
      then show ?thesis using Cons unfolding Anchor using assms apply simp unfolding matches_def
        by (simp add: eval_ternary_simps_simple(3))
    qed
  qed
qed

lemma and_each_true[simp]:
  assumes "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m)) = TernaryTrue"
  shows "filter_approx (and_each m l) \<gamma> p d = filter_approx l \<gamma> p d"
proof(induction l arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
  proof(cases d)
    case (Final x1)
    then show ?thesis by simp
  next
    case (Preliminary x2)
    then show ?thesis
    proof(cases a)
      case (PfRule x1)
      then show ?thesis using Preliminary assms apply simp
        by (metis Cons.IH matches_def matches_simps(1) ternary_to_bool_unknown_match_tac.simps(1))
    next
      case (Anchor x21 x22)
      then show ?thesis using Preliminary assms apply simp
        by (metis Cons.IH bunch_of_lemmata_about_matches(1) matches_def ternary_to_bool_unknown_match_tac.simps(1))
    qed
  qed
qed


lemma filter_final[simp]:
  assumes "filter_approx l \<gamma> p d = Final d'"
  shows "filter_approx (l@l') \<gamma> p d = Final d'"
proof(cases d)
  case (Final x1)
  then show ?thesis using assms by simp
next
  case (Preliminary x2)
  then show ?thesis using assms
  proof(induction l)
    case Nil
    then show ?case by simp
  next
    case (Cons a l)
    then show ?case by (simp add: filter_approx_chain)
  qed
qed

fun all_AnchorRules_P :: "('a anchor_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_AnchorRules_P P rs = (\<forall> l \<in> set rs. (case l of (Anchor r b) \<Rightarrow> P r \<and> all_AnchorRules_P P b | _ \<Rightarrow> True))"

fun all_AnchorRules_P' :: "('a anchor_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_AnchorRules_P' _ [] \<longleftrightarrow> True" |
"all_AnchorRules_P' P ((PfRule r)#ls) \<longleftrightarrow> all_AnchorRules_P' P ls" |
"all_AnchorRules_P' P ((Anchor r b)#ls) \<longleftrightarrow> P r \<and> all_AnchorRules_P' P b \<and> all_AnchorRules_P' P ls"

lemma "all_AnchorRules_P P l= all_AnchorRules_P' P l"
  by (induction P l rule: all_AnchorRules_P'.induct) auto

lemma all_AnchorRules_append[simp]:
  "all_AnchorRules_P P (xs @ ys) \<longleftrightarrow> all_AnchorRules_P P xs \<and> all_AnchorRules_P P ys"
  by (induction P xs rule: all_AnchorRules_P.induct) auto

definition no_anchors' :: "'a ruleset \<Rightarrow> bool" where
"no_anchors' rs = all_AnchorRules_P (\<lambda>r. False) rs"

lemma no_anchors_no_anchors'_eq:
 "no_anchors rs \<longleftrightarrow> no_anchors' rs"
  unfolding no_anchors'_def
proof(induction rs)
  case Nil
  then show ?case by auto
next
  case (Cons a rs)
  then show ?case by (cases a;auto)
qed


definition no_unknown_anchors :: "('a,'p) match_tac \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"no_unknown_anchors \<gamma> rs = all_AnchorRules_P
 (\<lambda>r. (\<forall> p. ternary_ternary_eval (map_match_tac (fst \<gamma>) p (anchor_rule.get_match r)) \<noteq> TernaryUnknown))
 rs"


fun all_PfRules_P :: "('a pf_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_PfRules_P P rs = (\<forall> l \<in> set rs. (case l of (PfRule r) \<Rightarrow> P r | (Anchor r b) \<Rightarrow> all_PfRules_P P b))"

fun all_PfRules_P' :: "('a pf_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_PfRules_P' _ [] \<longleftrightarrow> True" |
"all_PfRules_P' P ((PfRule r)#ls) \<longleftrightarrow> P r \<and> all_PfRules_P' P ls" |
"all_PfRules_P' P ((Anchor r b)#ls) \<longleftrightarrow> all_PfRules_P' P b \<and> all_PfRules_P' P ls"

lemma "all_PfRules_P P l= all_PfRules_P' P l"
  by (induction P l rule: all_PfRules_P'.induct) auto

lemma all_PfRules_append[simp]:
  "all_PfRules_P P (xs @ ys) \<longleftrightarrow> all_PfRules_P P xs \<and> all_PfRules_P P ys"
  by (induction P xs rule: all_PfRules_P.induct) auto

definition no_match_quick :: "'a ruleset \<Rightarrow> bool" where
"no_match_quick rs = all_PfRules_P (\<lambda>r. \<not>((pf_rule.get_action r) = action.Match \<and> pf_rule.get_quick r)) rs"

lemma decision_change:
  assumes "d \<noteq> d'"
      and "no_match_quick l"
      and "no_anchors l"
      and "unwrap_decision (filter_approx l (exact_match_tac, in_doubt_allow) p (Preliminary d)) = d'"
    shows "\<And>d'' .filter_approx l (exact_match_tac, in_doubt_allow) p (Preliminary d'') = filter_approx l (exact_match_tac, in_doubt_allow) p (Preliminary d)"
  using assms
proof(induction l arbitrary:d)
case Nil
  then show ?case by simp
next
  case (Cons a l)
  then have no_anchors:"no_anchors l" by simp
  have chain:"unwrap_decision (filter_approx (a # l) (exact_match_tac, in_doubt_allow) p (Preliminary d)) =
              unwrap_decision (filter_approx l (exact_match_tac, in_doubt_allow) p
               (filter_approx [a] (exact_match_tac, in_doubt_allow) p (Preliminary d)))"
    using filter_approx_chain by (metis append_Cons append_Nil)
  show ?case
  proof(cases a)
    case (PfRule r)
    then show ?thesis apply(cases d;cases d'; cases d'';cases "get_action r";cases "get_quick r";
cases "(ternary_ternary_eval (map_match_tac exact_match_tac p (pf_rule.get_match r)))")
      using Cons PfRule chain by (auto simp add:matches_def no_match_quick_def)
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons by simp
  qed
qed


lemma and_each_unknown[simp]:
  assumes unknown:"(ternary_ternary_eval (map_match_tac exact_match_tac p m)) = TernaryUnknown"
      and accepts:"unwrap_decision(filter_approx l (exact_match_tac, in_doubt_allow) p (Preliminary d)) = decision.Accept"
      and no_match_quick:"no_match_quick l"
      and no_anchors:"no_anchors l"
    shows "(filter_approx (and_each m l) (exact_match_tac,in_doubt_allow) p (Preliminary d)) =(filter_approx l (exact_match_tac, in_doubt_allow) p (Preliminary d))"
  using assms
proof(induction l arbitrary:d)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then have no_anchors_l:"no_anchors l" by auto
  have no_match_quick_l:"no_match_quick l" using Cons by (auto simp: no_match_quick_def)
  then show ?case
  proof(cases a)
    case (PfRule r)
    then show ?thesis
    proof(cases "get_quick r")
      case True
      then show ?thesis
      proof(cases "(ternary_ternary_eval (map_match_tac exact_match_tac p (pf_rule.get_match r)))")
        case TernaryTrue
        then show ?thesis apply(cases "get_action r") using Cons PfRule True TernaryTrue by (simp_all add:matches_def)
      next
        case TernaryFalse
        then show ?thesis using Cons PfRule True by (simp add:matches_def no_match_quick_def)
      next
        case TernaryUnknown
        then show ?thesis
        proof(cases "get_action r")
          case Pass
          then show ?thesis using Cons PfRule True TernaryUnknown by (simp add:matches_def)
        next
          case Match
          then show ?thesis using Cons PfRule True TernaryUnknown by(cases d;simp add:matches_def no_match_quick_def)
        next
          case Block
          then show ?thesis using Cons PfRule True TernaryUnknown by (simp add:matches_def no_match_quick_def)
        qed
      qed
    next
      case False
      then show ?thesis
      proof(cases "(ternary_ternary_eval (map_match_tac exact_match_tac p (pf_rule.get_match r)))")
        case TernaryTrue
        then show ?thesis
        proof(cases "get_action r")
          case Pass
          then show ?thesis using Cons PfRule False TernaryTrue by (simp add:matches_def no_match_quick_def)
        next
          case Match
          then show ?thesis using Cons PfRule False TernaryTrue by (simp add:matches_def no_match_quick_def)
        next
          case Block
          then show ?thesis using Cons PfRule False TernaryTrue apply(auto simp:matches_def no_match_quick_def)
            by (smt decision.distinct(1) decision_change no_match_quick_l)
        qed
      next
        case TernaryFalse
        then show ?thesis using Cons PfRule False by (simp add:matches_def no_match_quick_def)
      next
        case TernaryUnknown
        then show ?thesis
        proof(cases "get_action r")
          case Pass
          then show ?thesis using Cons PfRule False TernaryUnknown by (simp add:matches_def no_match_quick_def)
        next
          case Match
          then show ?thesis using Cons PfRule False TernaryUnknown by (cases d;simp add:matches_def no_match_quick_def)
        next
          case Block
          then show ?thesis using Cons PfRule False TernaryUnknown by (simp add:matches_def no_match_quick_def)
        qed
      qed
    qed
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons(5) by auto
  qed
qed

lemma matches_and_unknown_unknown[simp]:
  assumes "matches \<gamma> m1 a d p"
      and "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m2)) = TernaryUnknown"
    shows "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p (MatchAnd m2 m1))) = TernaryUnknown"
  using assms by (cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m1))"; auto simp:matches_def)

lemma not_matches_and_unknown_not_matches:
  assumes "\<not>matches \<gamma> m1 a d p"
      and "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m2)) = TernaryUnknown"
    shows "\<not>matches \<gamma> (MatchAnd m2 m1) a d p"
  using assms by (cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m1))"; auto simp:matches_def)

lemma and_each_unknown_reject[simp,intro]:
  assumes unknown:"(ternary_ternary_eval (map_match_tac exact_match_tac p m)) = TernaryUnknown"
      and rejects:"unwrap_decision(filter_approx l (exact_match_tac, in_doubt_allow) p (Preliminary d)) = decision.Reject"
      and no_match_quick:"no_match_quick l"
      and no_anchors:"no_anchors l"
    shows "(filter_approx (and_each m l) (exact_match_tac,in_doubt_allow) p (Preliminary d)) = (Preliminary d)"
  using assms
proof(induction l arbitrary:d)
case Nil
then show ?case by simp
next
  case (Cons a l)
  then show ?case
  proof(cases a)
    case (PfRule r)
    then show ?thesis using Cons  by (auto split:decision.splits simp:no_match_quick_def matches_def)
    proof(cases "matches (exact_match_tac,in_doubt_allow) (pf_rule.get_match r) (pf_rule.get_action r) d p")
      case True
      show ?thesis
      proof(cases "get_action r")
        case Pass
        then show ?thesis sorry
      next
        case Match
        then show ?thesis using Cons PfRule True by (auto split:decision.splits simp:no_match_quick_def)
      next
        case Block
        then have nomatch:"\<not>Matching_Ternary.matches (exact_match_tac,in_doubt_allow) (MatchAnd m (pf_rule.get_match r)) (get_action r) d p" using PfRule unknown apply (simp add: matches_def)
        then show ?thesis sorry
      qed

    next
      case False
      then have nomatch:"\<not>Matching_Ternary.matches (exact_match_tac,in_doubt_allow) (MatchAnd m (pf_rule.get_match r)) (get_action r) d p" using unknown by (simp add: not_matches_and_unknown_not_matches)
      then have "filter_approx (and_each m (a # l)) (exact_match_tac, in_doubt_allow) p (Preliminary d) =
                 filter_approx (and_each m l) (exact_match_tac, in_doubt_allow) p (Preliminary d)" using PfRule by (auto split:line.splits decision.splits)
      moreover have "unwrap_decision (filter_approx l (exact_match_tac, in_doubt_allow) p (Preliminary d)) = Reject" using PfRule False Cons(3) by (auto split:line.splits decision.splits)
      ultimately show ?thesis using Cons PfRule by (simp add:no_match_quick_def)
    qed
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons by auto
  qed
qed


lemma[simp]: "filter_approx [] \<gamma> p (filter_approx l \<gamma> p (Preliminary d)) = filter_approx l \<gamma> p (Preliminary d)"
  by (metis append.right_neutral filter_approx_chain)

lemma foo:
  assumes "filter_approx [(PfRule r)] \<gamma> p (Preliminary d) = (Final d')"
  shows "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d p \<and> (pf_rule.get_quick r) \<and> (action_to_decision (pf_rule.get_action r) d) = d'"
using assms
  by (smt decision_wrap.distinct(1) decision_wrap.inject(1) filter_approx.simps(1) filter_approx.simps(2) filter_approx.simps(3) line.simps(5))

(*
fun deciding_rule :: "'a ruleset \<Rightarrow> ('a,'p) match_tac \<Rightarrow> 'p \<Rightarrow> 'a pf_rule option \<Rightarrow> 'a pf_rule option" where
"deciding_rule [] _ _ a = a" |
"deciding_rule ((PfRule r)#ls) \<gamma> p a = (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p)
                                         then (if (get_quick r)
                                                then (Some r)
                                                else (deciding_rule ls \<gamma> p (Some r)))
                                         else (deciding_rule ls \<gamma> p a))"

lemma deciding_rule:
  assumes no_anchors:"no_anchors l"
      and deciding_rule:"deciding_rule l \<gamma> p None = (Some r)"
    shows "unwrap_decision (filter_approx l \<gamma> p d) = action_to_decision (pf_rule.get_action r)"
*)
lemma and_each_empty[simp]:
  assumes "and_each m l = []"
  shows "l = []"
  using assms
  by (induction l rule:and_each.induct) simp_all

fun no_pf_rules :: "'a ruleset \<Rightarrow> bool" where
"no_pf_rules [] = True" |
"no_pf_rules ((PfRule _)#ls) = False" |
"no_pf_rules ((Anchor _ b)#ls) = (no_pf_rules b \<and> no_pf_rules ls)"

lemma remove_anchors'_empty_no_pf_rules:
  assumes "remove_anchors' l = []"
  shows "no_pf_rules l"
  using assms
proof(induction l rule:remove_anchors'.induct)
case 1
then show ?case by simp
next
  case (2 r l rs)
  then show ?case by auto
next
  case (3 v rs)
  then show ?case by auto
qed

lemma no_pf_rules_no_change:
  assumes "no_pf_rules ls"
  shows "filter_approx ls m p d = d"
  using assms
proof(induction ls m p d rule:filter_approx.induct)
case (1 uu uv uw d)
then show ?case by simp
next
  case (2 ux uy v)
  then show ?case by simp
next
  case (3 l ls \<gamma> p d)
  then show ?case apply auto
    by (smt line.simps(6) list.discI list.sel(1) list.sel(3) no_pf_rules.elims(2))
qed

lemma and_each_preserves_no_match_quick:
  assumes "no_match_quick rules"
  shows "no_match_quick (and_each m rules)"
  using assms
proof(induction rules rule:and_each.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 m l ls)
  then have "no_match_quick [l]" by (simp add:no_match_quick_def)
  then have "no_match_quick [(and_line m l)]" apply (simp add:no_match_quick_def) apply(cases l) by simp_all
  moreover have "no_match_quick ls" using 2 by (simp add:no_match_quick_def)
  ultimately show ?case using 2 by (simp add:no_match_quick_def)
qed

lemma no_anchors_implies_no_unknown_anchors:
  assumes "no_anchors rs"
  shows "no_unknown_anchors \<gamma> rs"
  using assms
proof(induction rs)
  case Nil
  then show ?case by (simp add:no_unknown_anchors_def)
next
  case (Cons a rs)
  then show ?case by (cases a;simp add:no_unknown_anchors_def)
qed


lemma and_each_no_anchors_no_unknown_anchors:
  assumes "no_anchors rules"
  shows "no_unknown_anchors \<gamma> (and_each m rules)"
  using assms
proof(induction rules rule:and_each.induct)
  case (1 uu)
  then show ?case by (auto simp: no_unknown_anchors_def)
next
  case (2 m l ls)
  then have "no_anchors [l]" by simp
  then have "no_anchors' [l]" using no_anchors_no_anchors'_eq by blast
  then have *:"no_unknown_anchors \<gamma> [(and_line m l)]" unfolding no_anchors'_def no_unknown_anchors_def by (induction l) auto
  from 2 have "no_anchors ls" by simp
  then have "no_unknown_anchors \<gamma> ls" by (simp add:no_anchors_implies_no_unknown_anchors)
  then show ?case using 2 * by (simp add:no_unknown_anchors_def)
qed


lemma no_match_quick_append[simp]:
  "no_match_quick (l1@l2) \<longleftrightarrow> no_match_quick l1 \<and> no_match_quick l2"
  by (auto simp:no_match_quick_def)


lemma remove_anchors'_preserves_no_match_quick[simp]:
  assumes "no_match_quick rules"
  shows "no_match_quick (remove_anchors' rules)"
  using assms
proof(induction rules rule:remove_anchors'.induct)
case 1
then show ?case by simp
next
  case (2 r l rs)
  from 2(3) have "no_match_quick l" by (simp add:no_match_quick_def)
  moreover from 2(3) have "no_match_quick rs" by (simp add:no_match_quick_def)
  ultimately show ?case using 2 by (simp add:and_each_preserves_no_match_quick)
next
  case (3 v rs)
  then show ?case by (simp add:no_match_quick_def)
qed

lemma remove_anchors'_preserves_no_unknown_anchors[simp]:
  assumes "no_unknown_anchors \<gamma> rs"
  shows "no_unknown_anchors \<gamma> (remove_anchors' rs)"
  using assms
proof(induction rs rule:remove_anchors'.induct)
case 1
then show ?case by simp
next
  case (2 r l rs)
  then have "no_unknown_anchors \<gamma> (and_each (anchor_rule.get_match r) (remove_anchors' l))"
    using remove_anchors'_ok and_each_no_anchors_no_unknown_anchors by blast
  moreover have "no_unknown_anchors \<gamma> (remove_anchors' rs)"
    using remove_anchors'_ok no_anchors_implies_no_unknown_anchors by blast
  ultimately show ?case by (auto simp add:no_unknown_anchors_def)
next
  case (3 v rs)
  then show ?case by (simp add: no_unknown_anchors_def)
qed


lemma remove_anchors_preserves_semantics :
  assumes "no_match_quick rules"
      and "no_unknown_anchors (exact_match_tac, in_doubt_allow) rules"
  shows "pf_approx (remove_anchors' rules) (exact_match_tac, in_doubt_allow) packet = pf_approx rules (exact_match_tac, in_doubt_allow) packet"
proof(-)
  have "(filter_approx rules (exact_match_tac, in_doubt_allow) packet d = filter_approx (remove_anchors' rules) (exact_match_tac, in_doubt_allow) packet d)" for d using assms
  proof(induction rules arbitrary:d rule:remove_anchors'.induct)
    case 1
    then show ?case by simp
  next
    case (2 r l rs)
    then show ?case
    proof(cases "(ternary_ternary_eval (map_match_tac exact_match_tac packet (anchor_rule.get_match r)))")
      case TernaryTrue
      then show ?thesis using 2 apply (auto simp add: filter_approx_chain) by (cases d;auto simp add:matches_def no_match_quick_def no_unknown_anchors_def)
    next
      case TernaryFalse
      then show ?thesis using 2 apply (auto simp add: filter_approx_chain) by (cases d;auto simp add:matches_def no_match_quick_def no_unknown_anchors_def)
    next
      case TernaryUnknown
      then show ?thesis using 2(4) by (auto simp:no_unknown_anchors_def)
    qed
  next
    case (3 v rs)
    then show ?case apply (simp add:no_match_quick_def no_unknown_anchors_def)
      by (metis (no_types, hide_lams) append_Cons append_Nil filter_approx_chain)
  qed
  then show ?thesis by (simp add: filter_approx_to_pf_approx)
qed

lemma remove_suffix[simp]:
  assumes "\<not>matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) (unwrap_decision (filter_approx l \<gamma> p d)) p"
  shows "filter_approx (l@[(PfRule r)]) \<gamma> p d = filter_approx l \<gamma> p d"
proof(cases "filter_approx l \<gamma> p d")
  case (Final x1)
  then show ?thesis by (simp add: filter_approx_chain)
next
  case (Preliminary x2)
  then show ?thesis using assms by (simp add:filter_approx_chain)
qed

lemma remove_quick_preserves_semantics:
  assumes "no_anchors rules"
      and "no_match_quick rules"
    shows "pf_approx rules matcher packet = pf_approx (remove_quick rules) matcher packet"
  sorry

fun remove_matches :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_matches [] = []"
|"remove_matches ((PfRule r)#ls) = (if ((pf_rule.get_action r) = action.Match) then remove_matches ls else (PfRule r)#remove_matches ls)"
|"remove_matches (l#ls) = l#(remove_matches ls)"

lemma remove_matches_preverses_semantics:
  assumes "no_quick rules"
      and "no_anchors rules"
  shows "filter_approx rules matcher packet (Preliminary start_decision) = filter_approx (remove_matches rules) matcher packet (Preliminary start_decision)"
  using assms
  by (induction rules arbitrary:start_decision rule: remove_matches.induct; simp)

lemma remove_matches_ok:
  assumes "no_quick rules"
      and "no_anchors rules"
    shows "no_match (remove_matches rules)"
  using assms
  by (induction rules rule: remove_matches.induct; simp)
(*
fun pf_approx_to_simplefw :: "'a ruleset \<Rightarrow> 'a ruleset" where
"pf_approx_to_simplefw rules = (map to_simple_match (reverse (normalize_firewall (remove_quick (remove_anchors rules)))))"
*)
end