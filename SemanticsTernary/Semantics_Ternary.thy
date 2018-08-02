theory Semantics_Ternary
  imports Matching_Ternary
begin

fun filter_approx_spec :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter_approx_spec [] \<gamma> p d = d" |
"filter_approx_spec ((PfRule r)#ls) \<gamma> p d = (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p)
                                       then (if (pf_rule.get_quick r)
                                              then (action_to_decision (pf_rule.get_action r) d)
                                              else (filter_approx_spec ls \<gamma> p (action_to_decision (pf_rule.get_action r) d)))
                                       else filter_approx_spec ls \<gamma> p d)" |
"filter_approx_spec ((Anchor r b)#ls) \<gamma> p d = (if (matches
                                                     \<gamma>
                                                     (anchor_rule.get_match r)
                                                     (case (filter_approx_spec b \<gamma> p d) of
                                                             (* if the body accepts the anchor is equal to pass *)
                                                             Accept \<Rightarrow> Pass
                                                             (* if the body rejects the anchor is equal to block *)
                                                             | Reject \<Rightarrow> Block)
                                                     p)
                                               then (filter_approx_spec (b@ls) \<gamma> p d)
                                               else filter_approx_spec ls \<gamma> p d)"


fun filter_approx :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter_approx _ _ _ (Final d) = Final d" |
"filter_approx [] _ _ d = d" |
"filter_approx (l#ls) \<gamma> p (Preliminary d) =
  filter_approx ls \<gamma> p (case l of
                  (PfRule r) \<Rightarrow> (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p)
                                               then (if (get_quick r)
                                                      then (Final (action_to_decision (get_action r) d))
                                                      else (Preliminary (action_to_decision (get_action r) d)))
                                               else (Preliminary d))
                  | (Anchor r body) \<Rightarrow> (if (matches
                                              \<gamma>
                                              (anchor_rule.get_match r)
                                              (case (unwrap_decision (filter_approx body \<gamma> p (Preliminary d))) of
                                                      (* if the body accepts the anchor is equal to pass *)
                                                      Accept \<Rightarrow> Pass
                                                      (* if the body rejects the anchor is equal to block *)
                                                      | Reject \<Rightarrow> Block)
                                              p)
                                        then (filter_approx body \<gamma> p (Preliminary d))
                                        else (Preliminary d)))"

case_of_simps filter_approx_cases: filter_approx.simps


lemma filter_approx_chain:
  shows "filter_approx (l1@l2) \<gamma> p d = filter_approx l2 \<gamma> p (filter_approx l1 \<gamma> p d)"
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
    proof(cases "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p")
    case True
    then show ?thesis unfolding PfRule using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
next
  case (Anchor r l)
  then show ?thesis
  proof(cases "(matches
                m
                (anchor_rule.get_match r)
                (case (unwrap_decision (filter_approx body \<gamma> p d)) of
                        Accept \<Rightarrow> Pass
                        | Reject \<Rightarrow> Block)
                p)")
    case True
    then show ?thesis using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
qed
qed
qed

lemma "filter_approx_spec rules \<gamma> p start_decision = unwrap_decision (filter_approx rules \<gamma> p (Preliminary start_decision))"
proof(induction rules \<gamma> p start_decision rule: filter_approx_spec.induct)
  case (1 \<gamma> p d)
  then show ?case by simp
next
  case (2 r ls \<gamma> p d)
  then show ?case by simp
next
  case IH: (3 r b ls \<gamma> p d)
  then show ?case
  proof(cases "(matches
                \<gamma>
                (anchor_rule.get_match r)
                (case (filter_approx_spec b \<gamma> p d) of
                        Accept \<Rightarrow> Pass
                        | Reject \<Rightarrow> Block)
                p)")
    case True
    then show ?thesis using IH by (auto simp: filter_approx_chain)
  next
    case False
    then show ?thesis using IH by auto
  qed
qed

(* default behavior is Accept *)
definition pf_approx :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision" where
"pf_approx rules \<gamma> packet = unwrap_decision (filter_approx rules \<gamma> packet (Preliminary Accept))"
(*
definition filter' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter' rules \<gamma> d = filter rules (\<lambda>a p. \<gamma> a) () d"

lemma matches_equiv[simp]: "matches (\<lambda>a p. \<gamma> a packet) me () = matches \<gamma> me packet"
  by (induction me, auto)

lemma filter_filter'_eq[simp]: "filter' rules (\<lambda>a. \<gamma> a packet) d = filter rules \<gamma> packet d"
unfolding filter'_def
by (induction rules \<gamma> packet d rule: filter.induct) (auto split: line.splits)

definition pf' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision" where
"pf' rules \<gamma> = unwrap_decision (filter' rules \<gamma> (Preliminary Undecided))"

lemma "pf rules \<gamma> packet = pf' rules (\<lambda>a. \<gamma> a packet)"
  unfolding pf_def pf'_def
  by simp
*)

lemma filter_approx_to_pf_approx:
  assumes "\<forall> d. (filter_approx l1 m p d = filter_approx l2 m p d)"
  shows "pf_approx l1 m p = pf_approx l2 m p" unfolding pf_approx_def using assms by simp
end