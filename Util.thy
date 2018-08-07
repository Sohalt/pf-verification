theory Util
  imports PF
begin

(* ruleset transformations *)
definition ruleset_equiv :: "'a ruleset \<Rightarrow> 'a ruleset \<Rightarrow> bool" ("_ \<simeq> _") where
"(l1 \<simeq> l2) \<longleftrightarrow> (pf' l1 = pf' l2)"

lemma ruleset_equivI[intro]: "(\<And>\<gamma>. pf' l1 \<gamma> = pf' l2 \<gamma>) \<Longrightarrow> l1 \<simeq> l2"
  unfolding ruleset_equiv_def by auto

lemma ruleset_equiv_refl[intro, simp]: "l \<simeq> l" by auto

definition ok_transformation ::"('a ruleset \<Rightarrow> 'a ruleset) \<Rightarrow> bool"  where
"ok_transformation f \<longleftrightarrow> (\<forall> rules. (rules \<simeq> (f rules)))"

lemma ok_transformationI[intro]: "(\<And>rules. (rules \<simeq> (f rules))) \<Longrightarrow> ok_transformation f"
  unfolding ok_transformation_def by auto

lemma id_transformation[intro, simp]: "ok_transformation id" by auto

end