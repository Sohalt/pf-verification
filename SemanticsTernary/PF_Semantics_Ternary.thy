theory PF_Semantics_Ternary
  imports
PF_Matching_Ternary
PF_Unknown_Match_Tacs
"../PF_Optimize_Match_Exprs"
begin

fun filter_approx :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter_approx [] \<gamma> p d = d" |
"filter_approx ((PfRule r)#ls) \<gamma> p d =
  (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d p)
    then (if (pf_rule.get_quick r)
           then (action_to_decision (pf_rule.get_action r) d)
           else (filter_approx ls \<gamma> p (action_to_decision (pf_rule.get_action r) d)))
    else filter_approx ls \<gamma> p d)" |
"filter_approx ((Anchor r b)#ls) \<gamma> p d =
  (if (matches
         \<gamma>
         (anchor_rule.get_match r)
         (case (filter_approx b \<gamma> p d) of
                 (* if the body accepts, the anchor is equal to pass *)
                 Accept \<Rightarrow> Pass
                 (* if the body rejects, the anchor is equal to block *)
                 | Reject \<Rightarrow> Block)
         d
         p)
    then (filter_approx (b@ls) \<gamma> p d)
    else filter_approx ls \<gamma> p d)"


fun filter_approx' :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter_approx' _ _ _ (Final d) = Final d" |
"filter_approx' [] _ _ d = d" |
"filter_approx' (l#ls) \<gamma> p (Preliminary d) =
  filter_approx' ls \<gamma> p 
    (case l of
      (PfRule r) \<Rightarrow> (if (matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d p)
                                   then (if (get_quick r)
                                          then (Final (action_to_decision (get_action r) d))
                                          else (Preliminary (action_to_decision (get_action r) d)))
                                   else (Preliminary d))
      | (Anchor r body) \<Rightarrow> (if (matches
                                 \<gamma>
                                 (anchor_rule.get_match r)
                                 (case (unwrap_decision (filter_approx' body \<gamma> p (Preliminary d))) of
                                   (* if the body accepts the anchor is equal to pass *)
                                   Accept \<Rightarrow> Pass
                                   (* if the body rejects the anchor is equal to block *)
                                   | Reject \<Rightarrow> Block)
                                 d
                                 p)
                            then (filter_approx' body \<gamma> p (Preliminary d))
                            else (Preliminary d)))"

case_of_simps filter_approx'_cases: filter_approx'.simps

lemma filter_approx'_chain:
  shows "filter_approx' (l1@l2) \<gamma> p d = filter_approx' l2 \<gamma> p (filter_approx' l1 \<gamma> p d)"
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
    case (Preliminary x2)
    then show ?thesis
    proof(cases a)
      case (PfRule r)
      then show ?thesis using Preliminary IH
        by (cases "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d' p") auto
    next
      case (Anchor r l)
      then show ?thesis using Preliminary IH
        by (cases "(matches
                     m
                     (anchor_rule.get_match r)
                     (case (unwrap_decision (filter_approx' body \<gamma> p d)) of
                             Accept \<Rightarrow> Pass
                             | Reject \<Rightarrow> Block)
                     d'
                     p)") auto
    qed
  qed
qed

lemma "filter_approx rs \<gamma> p d = unwrap_decision (filter_approx' rs \<gamma> p (Preliminary d))"
proof(induction rs \<gamma> p d rule: filter_approx.induct)
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
                (case (filter_approx b \<gamma> p d) of
                        Accept \<Rightarrow> Pass
                        | Reject \<Rightarrow> Block)
                d
                p)")
    case True
    then show ?thesis using IH by (auto simp: filter_approx'_chain)
  next
    case False
    then show ?thesis using IH by auto
  qed
qed

(* default behavior is Accept *)
definition pf_approx :: "'a ruleset \<Rightarrow> ('a, 'p) match_tac \<Rightarrow> 'p \<Rightarrow> decision" where
"pf_approx rs \<gamma> p = unwrap_decision (filter_approx' rs \<gamma> p (Preliminary Accept))"

lemma filter_approx'_to_pf_approx:
  assumes "\<forall> d. (filter_approx' rs1 m p d = filter_approx' rs2 m p d)"
  shows "pf_approx rs1 m p = pf_approx rs2 m p" unfolding pf_approx_def using assms by simp


subsection\<open>Matching\<close> (* adapted from Iptables_Semantics.Semantics_Ternary *)
lemma optimize_matches_option_generic:
  assumes "simple_ruleset rs"
      and "\<forall> r \<in> set rs. (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) (pf_rule.get_action r) | _ \<Rightarrow> True)"
      and "(\<And>m m' a d. P m a \<Longrightarrow> f m = Some m' \<Longrightarrow> matches \<gamma> m' a d p = matches \<gamma> m a d p)"
      and "(\<And>m a d. P m a \<Longrightarrow> f m = None \<Longrightarrow> \<not> matches \<gamma> m a d p)"
    shows "pf_approx (optimize_matches_option f rs) \<gamma> p = pf_approx rs \<gamma> p"
proof(-)
  have "\<And>d. filter_approx' (optimize_matches_option f rs) \<gamma> p d = filter_approx' rs \<gamma> p d"
  using assms proof(induction rs arbitrary:d rule:optimize_matches_option.induct)
case (1 uu)
  then show ?case by simp
next
  case (2 f r rs)
  fix P assume P:"P (pf_rule.get_match r) (pf_rule.get_action r)"
  then show ?case
  proof(cases "f (pf_rule.get_match r)")
    case None
    then have "\<not>matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) (unwrap_decision d) p"
      using 2(1) 2(3) 2(6) apply (auto simp add: simple_ruleset_def)
      using "2.prems"(2) by auto
    then show ?thesis using 2(1) 2(3) 2(6) apply (auto simp add: simple_ruleset_def)
      by (cases d;simp add: "2.prems"(2) "2.prems"(3) None)
  next
    case (Some a)
    then have "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) (unwrap_decision d) p =
               matches \<gamma> a (pf_rule.get_action r) (unwrap_decision d) p"
      using 2(2) 2(3) 2(5) apply (auto simp add: simple_ruleset_def)
      using "2.prems"(2) apply auto[1]
      using "2.prems"(2) by auto
    then show ?thesis
    proof(cases "matches \<gamma> a (get_action r) (unwrap_decision d) p")
      case T1:True
      then have T2:"matches \<gamma> (pf_rule.get_match r) (get_action r) (unwrap_decision d) p"
        using \<open>matches \<gamma> (pf_rule.get_match r) (get_action r) (unwrap_decision d) p =
               matches \<gamma> a (get_action r) (unwrap_decision d) p\<close> by blast
      then show ?thesis 
      proof(cases d)
        case (Final x1)
        then show ?thesis by simp
      next
        case (Preliminary x2)
        then show ?thesis using T1 T2 "2.IH" "2.prems"(1) "2.prems"(2) Some P
          apply (simp add:simple_ruleset_def)
          using "2.prems"(3) "2.prems"(4) by blast
      qed
    next
      case F1:False
      then have F2:"\<not>matches \<gamma> (pf_rule.get_match r) (get_action r) (unwrap_decision d) p"
        using \<open>matches \<gamma> (pf_rule.get_match r) (get_action r) (unwrap_decision d) p =
               matches \<gamma> a (get_action r) (unwrap_decision d) p\<close> by blast
      then show ?thesis
      proof(cases d)
        case (Final x1)
        then show ?thesis by simp
      next
        case (Preliminary x2)
        then show ?thesis using F1 F2 "2.IH" "2.prems"(1) "2.prems"(2) Some P
          apply (simp add:simple_ruleset_def)
          using "2.prems"(3) "2.prems"(4) by blast
      qed
    qed
  qed
next
  case (3 a vb vc va)
  then show ?case by (auto simp add: simple_ruleset_def)
qed
  then show ?thesis by (simp add: filter_approx'_to_pf_approx)
qed


lemma optimize_matches_generic:
  assumes "simple_ruleset rs"
      and "\<forall> r \<in> set rs. (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) (pf_rule.get_action r) | _ \<Rightarrow> True)"
      and "(\<And>m a d. P m a \<Longrightarrow> matches \<gamma> (f m) a d p = matches \<gamma> m a d p)"
    shows "pf_approx (optimize_matches f rs) \<gamma> p = pf_approx rs \<gamma> p"
  unfolding optimize_matches_def
  apply(rule optimize_matches_option_generic)
     apply(simp add:assms(1))
  using assms(2) apply fast
   apply(simp split: if_split_asm)
  using assms(3) apply blast
  apply(simp split: if_split_asm)
  using assms(3) matcheq_matchNone_not_matches by fast

lemma optimize_matches:
  assumes "simple_ruleset rs"
      and "\<forall>m a d. matches \<gamma> (f m) a d p = matches \<gamma> m a d p"
    shows "pf_approx (optimize_matches f rs) \<gamma> p = pf_approx rs \<gamma> p"
  using assms optimize_matches_generic[where P="\<lambda>_ _. True"]
(* TODO more elegant *)
  by (simp add: \<open>\<And>rs p f \<gamma>. \<lbrakk>PF_Firewall_Common.simple_ruleset rs;
 \<forall>r\<in>set rs. case r of PfRule r \<Rightarrow> True | _ \<Rightarrow> True;
 \<And>m a d. True \<Longrightarrow> matches \<gamma> (f m) a d p = matches \<gamma> m a d p\<rbrakk> \<Longrightarrow> 
  pf_approx (optimize_matches f rs) \<gamma> p = pf_approx rs \<gamma> p\<close> line.case_eq_if)

lemma optimize_matches_preserves_semantics:
  assumes "simple_ruleset rs"
      and "good_matcher \<gamma>"
      and "\<forall>m a. matches \<gamma> (f m) a d p = matches \<gamma> m a d p"
    shows "pf_approx (optimize_matches f rs) \<gamma> p = pf_approx rs \<gamma> p"
proof(-)
  from assms(2) assms(3) have "\<And> m a d. a \<noteq> ActionMatch \<Longrightarrow> matches \<gamma> (f m) a d p = matches \<gamma> m a d p"
    apply (auto simp:good_matcher_def) by (metis matches_case)+
  then show ?thesis using assms optimize_matches_generic[where P="\<lambda> m a. a \<noteq> ActionMatch"]
(* TODO more elegant *)
    by (simp add: \<open>\<And>rs p f \<gamma>. \<lbrakk>PF_Firewall_Common.simple_ruleset rs; no_match rs;
 \<And>m a d. a \<noteq> ActionMatch \<Longrightarrow> matches \<gamma> (f m) a d p = matches \<gamma> m a d p\<rbrakk> \<Longrightarrow>
 pf_approx (optimize_matches f rs) \<gamma> p = pf_approx rs \<gamma> p\<close>
 PF_Firewall_Common.simple_ruleset_def)
qed

end