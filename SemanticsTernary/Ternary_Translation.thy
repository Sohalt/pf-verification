theory Ternary_Translation
  imports "../Pf_To_Simple_Firewall"
          Semantics_Ternary
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

(*
lemma and_unknown[simp]:
"eval_ternary_And TernaryUnknown e = TernaryUnknown"
*)

lemma and_each_unknown[simp]:
  assumes unknown:"(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m)) = TernaryUnknown"
      and accepts:"unwrap_decision(filter_approx l \<gamma> p d) = decision.Accept"
      and in_doubt_accept:"(snd \<gamma>) Pass p = True"
      and no_anchors:"no_anchors l"
    shows "filter_approx (and_each m l) \<gamma> p d = filter_approx l \<gamma> p d"
  using assms
proof(induction l arbitrary:d)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
  proof(cases a)
    case (PfRule r)
    then show ?thesis
    proof(cases d)
      case (Final x1)
      then show ?thesis by simp
    next
      case (Preliminary x2)
      then show ?thesis
      proof(cases "get_quick r")
        case True
        then show ?thesis using Cons PfRule Preliminary
          apply(cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p (pf_rule.get_match r)))";
cases "pf_rule.get_action r";auto simp add: matches_def)
          sorry
      next
        case False
        then show ?thesis using Cons PfRule Preliminary
          apply(cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p (pf_rule.get_match r)))";
cases "pf_rule.get_action r";auto simp add: matches_def)
          sorry
      qed
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
  shows "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p \<and> (pf_rule.get_quick r) \<and> (action_to_decision (pf_rule.get_action r) d) = d'"
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

lemma remove_anchors_preserves_semantics : "pf_approx (remove_anchors' rules) matcher packet = pf_approx rules matcher packet"
proof(-)
  have "(filter_approx rules matcher packet d = filter_approx (remove_anchors' rules) matcher packet d)" for d
  proof(induction rules arbitrary:d rule:remove_anchors'.induct)
    case 1
    then show ?case by simp
  next
    case (2 r l rs)
    then show ?case
    proof(cases "(ternary_ternary_eval (map_match_tac (fst matcher) packet (anchor_rule.get_match r)))")
      case TernaryTrue
      then show ?thesis using 2 apply (auto simp add: filter_approx_chain) by (cases d;auto simp add:matches_def)
    next
      case TernaryFalse
      then show ?thesis using 2 apply (auto simp add: filter_approx_chain) by (cases d;auto simp add:matches_def)
    next
      case TernaryUnknown
      then show ?thesis
      proof(cases d)
        case (Final x1)
        then show ?thesis by simp
      next
        case prelim:(Preliminary x2)
        then show ?thesis
        proof(cases "snd matcher Pass packet")
          case in_doubt_allow:True
          then show ?thesis
          proof(cases "filter_approx l matcher packet (Preliminary x2)")
            case (Final x1)
            then show ?thesis
            proof(cases x1)
              case Accept
              then show ?thesis using Final in_doubt_allow prelim TernaryUnknown apply auto
                apply (simp add: "2.IH"(1) filter_approx_chain remove_anchors'_ok)
                by (simp add: matches_def)
            next
              case Reject
              then show ?thesis using Final in_doubt_allow prelim TernaryUnknown apply auto sledgehammer sorry
            qed
          next
            case (Preliminary x22)
            then show ?thesis
            proof(cases x22)
              case Accept
              then show ?thesis using Preliminary in_doubt_allow prelim TernaryUnknown apply auto
                 apply (simp add: "2.IH"(1) "2.IH"(2) filter_approx_chain remove_anchors'_ok)
                by (simp add: matches_def)
            next
              case Reject
              then have "filter_approx l matcher packet (Preliminary x2) = Preliminary Reject"
                by(auto simp add: Preliminary)
              then show ?thesis using Preliminary in_doubt_allow prelim TernaryUnknown apply auto sorry
            qed
          qed
        next
          case in_doubt_deny:False
          then show ?thesis
          proof(cases "filter_approx l matcher packet (Preliminary x2)")
            case (Final x1)
            then show ?thesis
            proof(cases x1)
              case Accept
              then show ?thesis sorry
            next
              case Reject
              then show ?thesis sorry
            qed
          next
            case (Preliminary x2)
            then show ?thesis
            proof(cases x2)
              case Accept
              then show ?thesis sorry
            next
              case Reject
              then show ?thesis sorry
            qed
          qed
        qed
      qed
    qed
(*
            then have "unwrap_decision (filter_approx (remove_anchors' l) matcher packet (Preliminary x2)) = decision.Accept" using 2 Accept by auto
            then have "filter_approx (and_each (anchor_rule.get_match r) (remove_anchors' l)) matcher packet (Preliminary x2) =
                       filter_approx (remove_anchors' l) matcher packet (Preliminary x2)" sorry
            then show ?thesis unfolding Preliminary using 2 TernaryUnknown Accept in_doubt_allow by (simp add: matches_def filter_approx_chain)
          next
            case in_doubt_deny:False
            then show ?thesis sorry
          qed
*)
  next
    case (3 v rs)
    then show ?case apply simp
      by (metis append_Cons append_Nil filter_approx_chain)
  qed
  then show ?thesis by (simp add: filter_approx_to_pf_approx)
qed

lemma remove_suffix[simp]:
  assumes "\<not>matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p"
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
  shows "pf_approx rules matcher packet = pf_approx (remove_quick rules) matcher packet"
  sorry

fun remove_matches :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_matches [] = []"
|"remove_matches ((PfRule r)#ls) = (if ((pf_rule.get_action r) = action.Match) then remove_matches ls else (PfRule r)#remove_matches ls)"
|"remove_matches (l#ls) = l#(remove_matches ls)"

lemma remove_matches_ok:
  assumes "no_quick rules"
          "no_anchors rules"
  shows "filter_approx rules matcher packet (Preliminary start_decision) = filter_approx (remove_matches rules) matcher packet (Preliminary start_decision)"
  using assms
  by (induction rules arbitrary:start_decision rule: remove_matches.induct; simp)
(*
fun pf_approx_to_simplefw :: "'a ruleset \<Rightarrow> 'a ruleset" where
"pf_approx_to_simplefw rules = (map to_simple_match (reverse (normalize_firewall (remove_quick (remove_anchors rules)))))"
*)
end