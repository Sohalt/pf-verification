theory pfprefix_Semantics_Ternary
  imports pfprefix_Matching_Ternary
begin

fun filter_approx_spec :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter_approx_spec [] \<gamma> p d = d" |
"filter_approx_spec ((PfRule r)#ls) \<gamma> p d = (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d p)
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
                                                     d
                                                     p)
                                               then (filter_approx_spec (b@ls) \<gamma> p d)
                                               else filter_approx_spec ls \<gamma> p d)"


fun filter_approx :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter_approx _ _ _ (Final d) = Final d" |
"filter_approx [] _ _ d = d" |
"filter_approx (l#ls) \<gamma> p (Preliminary d) =
  filter_approx ls \<gamma> p (case l of
                  (PfRule r) \<Rightarrow> (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d p)
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
                                              d
                                              p)
                                        then (filter_approx body \<gamma> p (Preliminary d))
                                        else (Preliminary d)))"

case_of_simps filter_approx_cases: filter_approx.simps
(*
thm filter_approx.induct

lemma fai[induct pred: filter_approx]:
"(\<And>rules \<gamma> p d. P rules \<gamma> p (Final d)) \<Longrightarrow>
(\<And>\<gamma> p d. P [] \<gamma> p (Preliminary d)) \<Longrightarrow>
(\<And>l ls \<gamma> p d.
    (\<And>r' b'. l = Anchor r' b' \<Longrightarrow> P b' \<gamma> p (Preliminary d)) \<Longrightarrow>
    (\<And>r' b'.
        l = Anchor r' b' \<Longrightarrow>
        matches \<gamma> (anchor_rule.get_match r') (case unwrap_decision (filter_approx b' \<gamma> p (Preliminary d)) of Accept \<Rightarrow> Pass | Reject \<Rightarrow> Block)
         p \<Longrightarrow>
        P b' \<gamma> p (Preliminary d)) \<Longrightarrow>
    P ls \<gamma> p
     (case l of
      PfRule r \<Rightarrow>
        if matches \<gamma> (pf_rule.get_match r) (get_action r) p
        then if get_quick r then Final (action_to_decision (get_action r) d) else Preliminary (action_to_decision (get_action r) d)
        else Preliminary d
      | Anchor r body \<Rightarrow>
          if matches \<gamma> (anchor_rule.get_match r)
              (case unwrap_decision (filter_approx body \<gamma> p (Preliminary d)) of Accept \<Rightarrow> Pass | Reject \<Rightarrow> Block) p
          then filter_approx body \<gamma> p (Preliminary d) else Preliminary d) \<Longrightarrow>
    P (l # ls) \<gamma> p (Preliminary d)) \<Longrightarrow>
P rs \<gamma> p d" apply (induction rule:filter_approx.induct) *)


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
    proof(cases "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d' p")
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
                d'
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
                d
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

lemma filter_approx_to_pf_approx:
  assumes "\<forall> d. (filter_approx l1 m p d = filter_approx l2 m p d)"
  shows "pf_approx l1 m p = pf_approx l2 m p" unfolding pf_approx_def using assms by simp

(*
subsection\<open>Matching\<close>
lemma optimize_matches_option_generic:
  assumes "simple_ruleset rs"
      and "\<forall> r \<in> set rs. (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) (pf_rule.get_action r) | _ \<Rightarrow> True)"
      and "(\<And>m m' a. P m a \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a p = matches \<gamma> m a p)"
      and "(\<And>m a. P m a \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches \<gamma> m a p)"
    shows "pf_approx (optimize_matches_option f rs) \<gamma> p = pf_approx rs \<gamma> p"
proof(-)
  have "\<And>d. filter_approx (optimize_matches_option f rs) \<gamma> p d = filter_approx rs \<gamma> p d"
  using assms proof(induction rs arbitrary:d rule:optimize_matches_option.induct)
case (1 uu)
  then show ?case by simp
next
  case (2 f r rs)
  fix P assume P:"P (pf_rule.get_match r) (pf_rule.get_action r)"
  then show ?case
  proof(cases "f (pf_rule.get_match r)")
    case None
    then have "\<not>matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p" using 2(1) 2(3) 2(6) apply (auto simp add: simple_ruleset_def)
      using "2.prems"(2) by auto
    then show ?thesis using 2(1) 2(3) 2(6) apply (auto simp add: simple_ruleset_def)
      by (cases d;simp add: "2.prems"(2) "2.prems"(3) None)
  next
    case (Some a)
    then have "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p = matches \<gamma> a (pf_rule.get_action r) p" using 2(2) 2(3) 2(5) apply (auto simp add: simple_ruleset_def)
      using "2.prems"(2) apply auto[1]
      using "2.prems"(2) by auto
    then show ?thesis
    proof(cases "matches \<gamma> a (get_action r) p")
      case T1:True
      then have T2:"matches \<gamma> (pf_rule.get_match r) (get_action r) p"
        using \<open>matches \<gamma> (pf_rule.get_match r) (get_action r) p = matches \<gamma> a (get_action r) p\<close> by blast
      then show ?thesis 
      proof(cases d)
        case (Final x1)
        then show ?thesis by simp
      next
        case (Preliminary x2)
        then show ?thesis using T1 T2 "2.IH" "2.prems"(1) "2.prems"(2) Some P apply (simp add:simple_ruleset_def)
          using "2.prems"(3) "2.prems"(4) by blast
      qed
    next
      case F1:False
      then have F2:"\<not>matches \<gamma> (pf_rule.get_match r) (get_action r) p"
        using \<open>matches \<gamma> (pf_rule.get_match r) (get_action r) p = matches \<gamma> a (get_action r) p\<close> by blast
      then show ?thesis
      proof(cases d)
        case (Final x1)
        then show ?thesis by simp
      next
        case (Preliminary x2)
        then show ?thesis using F1 F2 "2.IH" "2.prems"(1) "2.prems"(2) Some P apply (simp add:simple_ruleset_def)
          using "2.prems"(3) "2.prems"(4) by blast
      qed
    qed
  qed
next
  case (3 a vb vc va)
  then show ?case by (auto simp add: simple_ruleset_def)
qed
  then show ?thesis by (simp add: filter_approx_to_pf_approx)
qed
*)

end