theory pfprefix_Stuff
  imports pfprefix_Ternary_Translation
begin

(* unused but might come in handy at some point *)

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
          case ActionMatch
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
          case ActionMatch
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
          case ActionMatch
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


lemma and_each_empty[simp]:
  assumes "and_each m l = []"
  shows "l = []"
  using assms
  by (induction l rule:and_each.induct) simp_all


fun no_pf_rules :: "'a ruleset \<Rightarrow> bool" where
"no_pf_rules [] = True" |
"no_pf_rules ((PfRule _)#ls) = False" |
"no_pf_rules ((Anchor _ b)#ls) = (no_pf_rules b \<and> no_pf_rules ls)"


lemma remove_anchors_empty_no_pf_rules:
  assumes "remove_anchors l = []"
  shows "no_pf_rules l"
  using assms
proof(induction l rule:remove_anchors.induct)
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


lemma remove_anchors_preserves_no_match_quick[simp]:
  assumes "no_match_quick rules"
  shows "no_match_quick (remove_anchors rules)"
  using assms
proof(induction rules rule:remove_anchors.induct)
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


lemma remove_anchors_preserves_no_unknown_anchors[simp]:
  assumes "no_unknown_anchors \<gamma> rs"
  shows "no_unknown_anchors \<gamma> (remove_anchors rs)"
  using assms
proof(induction rs rule:remove_anchors.induct)
case 1
then show ?case by simp
next
  case (2 r l rs)
  then have "no_unknown_anchors \<gamma> (and_each (anchor_rule.get_match r) (remove_anchors l))"
    using remove_anchors_ok and_each_no_anchors_no_unknown_anchors by blast
  moreover have "no_unknown_anchors \<gamma> (remove_anchors rs)"
    using remove_anchors_ok no_anchors_implies_no_unknown_anchors by blast
  ultimately show ?case by (auto simp add:no_unknown_anchors_def)
next
  case (3 v rs)
  then show ?case by (simp add: no_unknown_anchors_def)
qed


end