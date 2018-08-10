theory pfprefix_Util
  imports pfprefix_PF
begin

(* definitions without packet type 'p *)
definition filter'' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter'' rules \<gamma> d = filter' rules (\<lambda>a p. \<gamma> a) () d"

lemma matches_equiv[simp]: "matches (\<lambda>a p. \<gamma> a packet) me () = matches \<gamma> me packet"
  by (induction me, auto)

lemma filter_filter''_eq[simp]: "filter'' rules (\<lambda>a. \<gamma> a packet) d = filter' rules \<gamma> packet d"
unfolding filter''_def
by (induction rules \<gamma> packet d rule: filter'.induct) (auto split: line.splits)

(* default behavior is Accept *)
definition pf' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision" where
"pf' rules \<gamma> = unwrap_decision (filter'' rules \<gamma> (Preliminary Accept))"

lemma "pf rules \<gamma> packet = pf' rules (\<lambda>a. \<gamma> a packet)"
  unfolding pf_def pf'_def
  by simp

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