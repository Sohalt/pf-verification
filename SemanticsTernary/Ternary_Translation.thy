theory Ternary_Translation
  imports "../Pf_To_Simple_Firewall"
          SemanticsTernary
begin

lemma filter_approx_to_pf_approx:
  assumes "\<forall> d. (filter_approx l1 m p d = filter_approx l2 m p d)"
  shows "pf_approx l1 m p = pf_approx l2 m p" unfolding pf_approx_def using assms by simp

lemma filter_approx_add_equiv_prefix :
  assumes "filter_approx l1 m p d = filter_approx l2 m p d"
          "\<And>d. filter_approx l3 m p d = filter_approx l4 m p d"
  shows "filter_approx (l1@l3) m p d = filter_approx (l2@l4) m p d"
proof -
    have "filter_approx (l1@l3) m p d = filter_approx l3 m p (filter_approx l1 m p d)" by (simp add: filter_approx_chain)
    moreover have "filter_approx (l2@l4) m p d = filter_approx l4 m p (filter_approx l2 m p d)" by (simp add: filter_approx_chain)
    ultimately show ?thesis using assms by auto
  qed

lemma filter_approx_add_same_prefix :
  assumes "\<And>d. filter_approx l1 m p d = filter_approx l2 m p d"
  shows "filter_approx (l@l1) m p d = filter_approx (l@l2) m p d"
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



lemma[simp]: "filter_approx [] m p (filter_approx l m p (Preliminary d)) = filter_approx l m p (Preliminary d)"
  by (metis append.right_neutral filter_approx_chain)

lemma foo:
  assumes "filter_approx [(PfRule r)] m p (Preliminary d) = (Final d')"
  shows "matches m (pf_rule.get_match r) (pf_rule.get_action r) p \<and> (pf_rule.get_quick r) \<and> (action_to_decision (pf_rule.get_action r) d) = d'"
using assms
  by (smt decision_wrap.distinct(1) decision_wrap.inject(1) filter_approx.simps(1) filter_approx.simps(2) filter_approx.simps(3) line.simps(5))

fun deciding_rule :: "'a ruleset \<Rightarrow> ('a,'p) match_tac \<Rightarrow> 'p \<Rightarrow> 'a pf_rule option \<Rightarrow> 'a pf_rule option" where
"deciding_rule [] _ _ a = a" |
"deciding_rule ((PfRule r)#ls) \<gamma> p a = (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p) 
                                         then (if (get_quick r)
                                                then (Some r)
                                                else (deciding_rule ls \<gamma> p (Some r)))
                                         else (deciding_rule ls \<gamma> p a))"

lemma deciding_rule:
  assumes no_anchors:"no_anchors l"
      and deciding_rule:"deciding_rule l m p None = (Some r)"
    shows "unwrap_decision (filter_approx l m p d) = action_to_decision (pf_rule.get_action r)"

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
        case (Preliminary x2)
        then show ?thesis
        proof(cases "unwrap_decision (filter_approx l matcher packet (Preliminary x2))")
          case Accept
          then show ?thesis
          proof(cases "snd matcher Pass packet")
            case True
            then have "unwrap_decision (filter_approx (remove_anchors' l) matcher packet (Preliminary x2)) = decision.Accept" using 2 Accept by auto
            then have "filter_approx (and_each (anchor_rule.get_match r) (remove_anchors' l)) matcher packet (Preliminary x2) =
                       filter_approx (remove_anchors' l) matcher packet (Preliminary x2)" sorry
            then show ?thesis unfolding Preliminary using 2 TernaryUnknown Accept True by (simp add: matches_def filter_approx_chain)
          next
            case False
            then show ?thesis sorry
          qed
        next
          case Reject
          then show ?thesis sorry
        qed
      qed     
    qed
  next
    case (3 v rs)
    then show ?case apply simp
      by (metis append_Cons append_Nil filter_approx_chain)
  qed
  then show ?thesis by (simp add: filter_approx_to_pf_approx)
qed

lemma remove_anchors_preserves_semantics : "pf_approx (remove_anchors rules) matcher packet = pf_approx rules matcher packet"
proof(-)
  have "(filter_approx rules matcher packet d = filter_approx (remove_anchors rules) matcher packet d)" for d
proof (induction rules arbitrary: d)
  case Nil
  then show ?case by auto
next
  case IH: (Cons a rules)
  then show ?case
  proof(cases d)
    case (Final x1)
    then show ?thesis by auto
  next
    case (Preliminary x2)
    then show ?thesis
  proof (cases a)
    case (PfRule r)
    then show ?thesis unfolding PfRule using IH by (cases d, auto)
  next
    case (Anchor r ls)
    then have "filter_approx [(Anchor r ls)] matcher packet d =
               filter_approx (and_each (anchor_rule.get_match r) ls) matcher packet d"
    proof(cases "(ternary_ternary_eval (map_match_tac (fst matcher) packet (anchor_rule.get_match r)))")
      case TernaryTrue
      then have "filter_approx (and_each (anchor_rule.get_match r) ls) matcher packet (Preliminary x2)
                 = filter_approx ls matcher packet (Preliminary x2)" by auto
      moreover have "filter_approx [Anchor r ls] matcher packet (Preliminary x2)
                 = filter_approx ls matcher packet (Preliminary x2)"
        by (simp add: TernaryTrue matches_def)
      ultimately show ?thesis unfolding Preliminary
        by simp
    next
      case TernaryFalse
      then show ?thesis unfolding Preliminary apply auto unfolding matches_def by auto
    next
      case TernaryUnknown
      then show ?thesis
      proof(cases "(unwrap_decision (filter_approx ls matcher packet d))")
        case Accept
        then show ?thesis
        proof(cases "(snd matcher) Pass packet")
          case True
          then show ?thesis using Accept TernaryUnknown unfolding Preliminary apply (simp add: matches_def) sorry
        next
          case False
          then show ?thesis using Accept TernaryUnknown unfolding Preliminary apply (simp add: matches_def)  sorry
        qed
      next
        case Reject
        then show ?thesis
        proof(cases "(snd matcher) Block packet")
          case True
          then show ?thesis using Reject TernaryUnknown unfolding Preliminary apply (simp add: matches_def) sorry
        next
          case False
          then show ?thesis using Reject TernaryUnknown unfolding Preliminary apply (simp add: matches_def) sorry
        qed
      qed
    qed
    then have "filter_approx ([Anchor r ls] @ rules) matcher packet d = filter_approx (and_each (get_match r) ls @ remove_anchors rules) matcher packet d"
      apply (rule filter_approx_add_equiv_prefix)
      using IH by auto

    then show ?thesis unfolding Anchor
      by simp
  qed
  qed
qed
  then show ?thesis
    by (simp add: filter_approx_to_pf_approx)
qed

lemma remove_all_anchors_remove_anchors_idempotent:"pf_approx (remove_all_anchors (remove_anchors rules)) matcher packet = pf_approx (remove_all_anchors rules) matcher packet"
  by (metis le0 le_antisym no_anchors_0_anchors remove_all_anchors.simps remove_anchors_only_subtracts remove_anchors_preserves_semantics)

lemma remove_all_anchors_preserves_semantics : "pf_approx rules matcher packet = pf_approx (remove_all_anchors rules) matcher packet"
proof(induction rules rule: remove_all_anchors.induct)
  case (1 rules)
  then show ?case
  proof(cases "no_anchors rules")
    case True
    then show ?thesis by simp
  next
    case False
    then have "pf_approx (remove_anchors rules) matcher packet = pf_approx (remove_all_anchors (remove_anchors rules)) matcher packet" by (simp add: 1)
    moreover have "pf_approx (remove_all_anchors (remove_anchors rules)) matcher packet =  pf_approx (remove_all_anchors rules) matcher packet"
      by (meson remove_all_anchors_remove_anchors_idempotent)
    ultimately show ?thesis by (simp add: remove_anchors_preserves_semantics)
  qed
qed

lemma remove_suffix[simp]:
  assumes "\<not>matches m (pf_rule.get_match r) (pf_rule.get_action r) p"
  shows "filter_approx (l@[(PfRule r)]) m p d = filter_approx l m p d"
proof(cases "filter_approx l m p d")
  case (Final x1)
  then show ?thesis by (simp add: filter_approx_chain)
next
  case (Preliminary x2)
  then show ?thesis using assms by (simp add:filter_approx_chain)
qed

lemma remove_single_quick_preserves_semantics:
  assumes "no_anchors rules"
  shows "pf_approx rules matcher packet = pf_approx (remove_single_quick rules) matcher packet"
proof(-)
  from assms have "(unwrap_decision (filter_approx rules matcher packet d) = unwrap_decision (filter_approx (remove_single_quick rules) matcher packet d))" for d
  proof(induction rules arbitrary: d)
    case Nil
    then show ?case by simp
  next
    case IH: (Cons a rules)
    then show ?case
    proof(cases d)
      case (Final x1)
      then show ?thesis by simp
    next
      case (Preliminary x2)
      then show ?thesis
      proof(cases a)
        case (PfRule r)
        then show ?thesis
        proof(cases "get_quick r")
          case Quick:True
          then show ?thesis
          proof(cases "matches matcher (pf_rule.get_match r) (pf_rule.get_action r) packet")
            case True
            then show ?thesis unfolding PfRule Preliminary using Quick by (simp add:filter_approx_chain)
          next
            case False
            then show ?thesis unfolding PfRule Preliminary using Quick by auto
          qed
        next
          case False
          then show ?thesis unfolding PfRule using IH by (cases d, auto)
        qed
      next
        case (Anchor x31 x32)
        then show ?thesis using IH by auto
      qed
    qed
  qed
  then show ?thesis by (simp add: pf_approx_def)
qed

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