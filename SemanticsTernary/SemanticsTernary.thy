theory SemanticsTernary
  imports Matching_Ternary
begin

fun filter_approx_spec :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter_approx_spec [] m p d = d" |
"filter_approx_spec ((PfRule r)#ls) m p d = (if (matches m (pf_rule.get_match r) (pf_rule.get_action r) p)
                                       then (if (pf_rule.get_quick r)
                                              then (action_to_decision (pf_rule.get_action r) d)
                                              else (filter_approx_spec ls m p (action_to_decision (pf_rule.get_action r) d)))
                                       else filter_approx_spec ls m p d)" |
"filter_approx_spec ((Anchor r b)#ls) m p d = (if (matches_anchor m (anchor_rule.get_match r) p)
                                         then (filter_approx_spec (b@ls) m p d)
                                         else filter_approx_spec ls m p d)"

fun filter_approx :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter_approx _ _ _ (Final d) = Final d" |
"filter_approx [] _ _ d = d" |
"filter_approx (l#ls) m p (Preliminary d) =
  filter_approx ls m p (case l of
                  (PfRule r) \<Rightarrow> (if (matches m (pf_rule.get_match r) (pf_rule.get_action r) p)
                                               then (if (get_quick r)
                                                      then (Final (action_to_decision (get_action r) d))
                                                      else (Preliminary (action_to_decision (get_action r) d)))
                                               else (Preliminary d))
                  | (Anchor r body) \<Rightarrow> (if (matches_anchor m (anchor_rule.get_match r) p)
                                                    then filter_approx (body) m p (Preliminary d)
                                                    else (Preliminary d)))"

case_of_simps filter_approx_cases: filter_approx.simps


fun unwrap_decision :: "decision_wrap \<Rightarrow> decision" where
"unwrap_decision (Final d) = d"
|"unwrap_decision (Preliminary d) = d"

case_of_simps unwrap_decision_cases: unwrap_decision.simps

lemma filter_approx_chain:
  shows "filter_approx (l1@l2) m p d = filter_approx l2 m p (filter_approx l1 m p d)"
proof(induction l1 arbitrary: d)
  case Nil
  then show ?case
  proof(cases d)
    case (Final x1)
    then show ?thesis by simp
  next
    case (Preliminary x2)
    then show ?thesis by simp
  qed
next
  case IH:(Cons a l1)
  then show ?case
  proof(cases d)
    case (Final x1)
    then show ?thesis by simp
  next
    case Prem: (Preliminary x2)
    then show ?thesis
    proof(cases a)
case (PfRule r)
  then show ?thesis
    proof(cases "matches m (pf_rule.get_match r) (pf_rule.get_action r) p")
    case True
    then show ?thesis unfolding PfRule using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
next
  case (Anchor r l)
  then show ?thesis
  proof(cases "matches_anchor m (anchor_rule.get_match r) p")
    case True
    then show ?thesis using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
qed
qed
qed

lemma "filter_approx_spec rules m p start_decision = unwrap_decision (filter_approx rules m p (Preliminary start_decision))"
proof(induction rules m p start_decision rule: filter_approx_spec.induct)
  case (1 m p d)
  then show ?case by simp
next
  case (2 r ls m p d)
  then show ?case by simp
next
  case IH: (3 r b ls m p d)
  then show ?case
  proof(cases "matches_anchor m (anchor_rule.get_match r) p")
    case True
    then show ?thesis using IH by (auto simp: filter_approx_chain)
  next
    case False
    then show ?thesis using IH by auto
  qed
qed

(* default behavior is Accept *)
definition pf_approx :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision" where
"pf_approx rules m packet = unwrap_decision (filter_approx rules m packet (Preliminary Accept))"
(*
definition filter' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter' rules m d = filter rules (\<lambda>a p. m a) () d"

lemma matches_equiv[simp]: "matches (\<lambda>a p. m a packet) me () = matches m me packet"
  by (induction me, auto)

lemma filter_filter'_eq[simp]: "filter' rules (\<lambda>a. m a packet) d = filter rules m packet d"
unfolding filter'_def
by (induction rules m packet d rule: filter.induct) (auto split: line.splits)

definition pf' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision" where
"pf' rules m = unwrap_decision (filter' rules m (Preliminary Undecided))"

lemma "pf rules m packet = pf' rules (\<lambda>a. m a packet)"
  unfolding pf_def pf'_def
  by simp
*)
end