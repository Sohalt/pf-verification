theory PF_Optimize_Match_Exprs
  imports PF_Firewall_Common
"SemanticsTernary/PF_Predicates"
begin

text\<open>optimizing match expressions\<close> (* adapted from Iptables_Semantics.Firewall_Common *)

fun optimize_matches_option ::
"('a match_expr \<Rightarrow> 'a match_expr option) \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
"optimize_matches_option _ [] = []" |
"optimize_matches_option f (PfRule r#rs) =
  (case f (pf_rule.get_match r) of
    None \<Rightarrow> optimize_matches_option f rs 
    | Some m \<Rightarrow> (PfRule (r\<lparr>pf_rule.get_match := m\<rparr>))#optimize_matches_option f rs)"

lemma optimize_matches_option_simple_ruleset:
"simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches_option f rs)"
  proof(induction rs rule:optimize_matches_option.induct)
  qed(simp_all add: simple_ruleset_def split: option.split)

lemma optimize_matches_option_preserves:
  assumes simple_ruleset: "simple_ruleset rs"
      and f_Some: "(\<And> r m. (PfRule r) \<in> set rs \<and> f (pf_rule.get_match r) = Some m \<Longrightarrow> P m)"
    shows "(\<forall> r \<in> set (optimize_matches_option f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) | _ \<Rightarrow> True))"
  using assms
proof(induction rs rule: optimize_matches_option.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 f r rs)
  then show ?case
  proof(cases "f (pf_rule.get_match r)")
    case None
    then show ?thesis using None 2 by (auto simp add: simple_ruleset_def)
  next
    case (Some a)
    then show ?thesis using Some 2 by (auto simp add: simple_ruleset_def)
  qed
next
  case (3 a vb vc va)
  then show ?case by (auto simp add: simple_ruleset_def)
qed

lemma optimize_matches_option_append: 
  assumes "simple_ruleset rs1"
      and "simple_ruleset rs2"
    shows "optimize_matches_option f (rs1@rs2) =
           optimize_matches_option f rs1 @ optimize_matches_option f rs2"
  using assms by (induction rs1 rule: optimize_matches_option.induct)
                 (auto simp: simple_ruleset_def split: option.split)



definition optimize_matches :: "('a match_expr \<Rightarrow> 'a match_expr) \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
  "optimize_matches f rs =
    optimize_matches_option (\<lambda>m. (if matcheq_matchNone (f m) then None else Some (f m))) rs"

lemma optimize_matches_empty[simp]:
"optimize_matches f [] = []"
  unfolding optimize_matches_def by simp

lemma optimize_matches_append:
  assumes "simple_ruleset rs1"
      and "simple_ruleset rs2"
    shows "optimize_matches f (rs1@rs2) = optimize_matches f rs1 @ optimize_matches f rs2"
  using assms by(simp add: optimize_matches_def optimize_matches_option_append)

lemma optimize_matches_preserves:
  assumes "simple_ruleset rs"
  shows  "(\<And> r. (PfRule r) \<in> set rs \<Longrightarrow> P (f (pf_rule.get_match r))) \<Longrightarrow>
    \<forall> r \<in> set (optimize_matches f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) | _ \<Rightarrow> True)"
  using assms
  unfolding optimize_matches_def
  apply(rule optimize_matches_option_preserves)
  by(auto split: if_split_asm)

lemma optimize_matches_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches f rs)"
  by(simp add: optimize_matches_def optimize_matches_option_simple_ruleset)


fun optimize_matches_a :: "(action \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr) \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
"optimize_matches_a _ [] = []" |
"optimize_matches_a f (PfRule r#rs) = 
(PfRule (r\<lparr>pf_rule.get_match := f (pf_rule.get_action r) (pf_rule.get_match r)\<rparr>))#optimize_matches_a f rs"

lemma optimize_matches_a_simple_ruleset:
"simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches_a f rs)"
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
  proof(cases a)
    case (PfRule x1)
    then have "simple_ruleset rs" using Cons(2) by (simp add: simple_ruleset_def)
    then show ?thesis using Cons PfRule by (simp add:simple_ruleset_def)
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons(2) by (auto simp add: simple_ruleset_def)
  qed
qed

lemma optimize_matches_a_simple_ruleset_eq:
  "simple_ruleset rs \<Longrightarrow> (\<And> m a. a = Pass \<or> a = Block \<Longrightarrow> f1 a m = f2 a m)
    \<Longrightarrow> optimize_matches_a f1 rs = optimize_matches_a f2 rs"
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
  proof(cases a)
    case (PfRule x1)
    then show ?thesis using Cons by (auto simp add:simple_ruleset_def) (cases "get_action x1";auto)
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons by (auto simp add:simple_ruleset_def)
  qed
qed

lemma optimize_matches_a_preserves:
  assumes "simple_ruleset rs"
  shows "(\<And> r. (PfRule r) \<in> set rs \<Longrightarrow> P (f (pf_rule.get_action r) (pf_rule.get_match r)))
    \<Longrightarrow> \<forall> r \<in> set (optimize_matches_a f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) 
                                                        | _ \<Rightarrow> True)"
  using assms
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case using Cons by (cases a; auto simp add: simple_ruleset_def)
qed


lemma simple_ruleset_wf_ruleset:
  assumes "simple_ruleset rs"
      and "all_PfRules_P (\<lambda>r. good_match_expr ctx (pf_rule.get_match r)) rs"
    shows "wf_ruleset ctx rs"
proof(-)
  have "all_AnchorRules_P (\<lambda>r. good_match_expr ctx (anchor_rule.get_match r)) rs"
    using assms unfolding simple_ruleset_def
    by (simp add: line.case_eq_if)
  then show ?thesis using assms(2) by (simp add:wf_ruleset_def)
qed


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