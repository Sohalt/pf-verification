theory Util
  imports PF
begin

(* ruleset transformations *)
definition ruleset_equiv :: "'a ruleset \<Rightarrow> 'a ruleset \<Rightarrow> bool" ("_ \<simeq> _") where
"(l1 \<simeq> l2) \<longleftrightarrow> (pf' l1 = pf' l2)"

lemma ruleset_equivI[intro]: "(\<And>m. pf' l1 m = pf' l2 m) \<Longrightarrow> l1 \<simeq> l2"
  unfolding ruleset_equiv_def by auto

lemma ruleset_equiv_refl[intro, simp]: "l \<simeq> l" by auto

definition ok_transformation ::"('a ruleset \<Rightarrow> 'a ruleset) \<Rightarrow> bool"  where
"ok_transformation f \<longleftrightarrow> (\<forall> rules. (rules \<simeq> (f rules)))"

lemma ok_transformationI[intro]: "(\<And>rules. (rules \<simeq> (f rules))) \<Longrightarrow> ok_transformation f"
  unfolding ok_transformation_def by auto

lemma id_transformation[intro, simp]: "ok_transformation id" by auto


(* some lemmas *)
lemma find_split:
  assumes "find P xs = Some x"
  shows "\<exists>xs1 xs2. xs = xs1 @ x # xs2 \<and> (\<forall>x \<in> set xs1. \<not> P x)"
  using assms
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs')
  show ?case
  proof(cases "P a")
    case True
      have "a#xs' = []@a#xs' \<and> (\<forall>x \<in> set []. \<not> P x)" by auto
      then show ?thesis sorry
  next
    case False
    then obtain xs1 xs2 where "xs' = xs1 @ x # xs2 \<and> (\<forall>x\<in>set xs1. \<not> P x)" using Cons by auto
    then have "a#xs' = (a#xs1)@x#xs2 \<and> (\<forall>x\<in>set (a#xs1). \<not> P x)" using False by auto
    then show ?thesis sorry
  qed
qed

end