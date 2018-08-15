theory PF_Foo
  imports PF_Firewall_Common
"SemanticsTernary/PF_Predicates"
begin

lemma simple_ruleset_all_AnchorRules_P[simp,intro]:
  "simple_ruleset rs \<Longrightarrow> all_AnchorRules_P P rs = True"
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case by (cases a) (simp add:simple_ruleset_def)+ 
qed


lemma simple_ruleset_all_PfRules_P:
  assumes "simple_ruleset rs"
  shows "all_PfRules_P P rs \<longleftrightarrow> (\<forall> r. (PfRule r) \<in> set rs \<longrightarrow> P r)"
  using assms proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
  proof(cases a)
  case (PfRule r)
    then show ?thesis
    proof(cases "P r")
      case True
      then show ?thesis using Cons PfRule by (simp add:simple_ruleset_def)
    next
      case False
      then show ?thesis using PfRule apply simp by blast
    qed
  next
  case (Anchor x21 x22)
    then show ?thesis using Cons by (auto simp:simple_ruleset_def)
  qed
qed

lemma optimize_matches_preserves_all_PfRules_P:
  assumes "simple_ruleset rs"
  shows "all_PfRules_P (\<lambda>r. (P (f (pf_rule.get_match r)))) rs \<Longrightarrow> 
         all_PfRules_P (\<lambda>r. P (pf_rule.get_match r)) (optimize_matches f rs)"
proof(-)
  assume "all_PfRules_P (\<lambda>r. (P (f (pf_rule.get_match r)))) rs"
  then have "\<And>r. (PfRule r) \<in> set rs \<Longrightarrow> P (f (pf_rule.get_match r))"
    using assms simple_ruleset_all_PfRules_P by auto
  then have "\<forall> r \<in> set (optimize_matches f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) | _ \<Rightarrow> True)"
    using optimize_matches_preserves assms by blast
  then show ?thesis using assms simple_ruleset_all_PfRules_P optimize_matches_simple_ruleset
    by(smt line.simps(5))
qed

lemma optimize_matches_preserves_all_PfRules_P':
  assumes "simple_ruleset rs"
    and "\<And>m. P (f m)"
  shows "all_PfRules_P (\<lambda>r. P (pf_rule.get_match r)) (optimize_matches f rs)"
proof(-)
  have "\<And>r. (PfRule r) \<in> set rs \<Longrightarrow> P (f (pf_rule.get_match r))" using assms by auto
  then have "\<forall> r \<in> set (optimize_matches f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) | _ \<Rightarrow> True)"
    using optimize_matches_preserves assms by blast
  then show ?thesis using assms simple_ruleset_all_PfRules_P optimize_matches_simple_ruleset
    by(smt line.simps(5))
qed

end