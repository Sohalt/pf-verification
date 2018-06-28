theory Pf_To_Simple_Firewall
imports PF
        Simple_Firewall.SimpleFw_Semantics
begin

fun and_line :: "'a match_expr \<Rightarrow> 'a line \<Rightarrow> 'a line" where
"and_line m Option =Option"|
"and_line m (PfRule r) = (PfRule (r\<lparr>pf_rule2.get_match := (MatchAnd m (pf_rule2.get_match r))\<rparr>))"|
"and_line m (Anchor r l) = (Anchor (r\<lparr>anchor_rule2.get_match := (MatchAnd m (anchor_rule2.get_match r))\<rparr>) l)"

fun and_each :: "'a match_expr \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
"and_each _ [] = []"|
"and_each m (l#ls) = (and_line m l)#(and_each m ls)"

fun remove_anchors :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_anchors [] = []"|
"remove_anchors ((Anchor r l) # rs) = (and_each (anchor_rule2.get_match r) l) @ (remove_anchors rs)"|
"remove_anchors (r#rs) = r#(remove_anchors rs)"


fun is_quick_rule :: "'a line \<Rightarrow> bool" where
"is_quick_rule (PfRule r) = (get_quick r)"
| "is_quick_rule _ = False"

lemma filter_chain:
  shows "filter (l1@l2) m p d = filter l2 m p (filter l1 m p d)"
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
      case Option
then show ?thesis using Prem IH by simp
next
case (PfRule r)
  then show ?thesis
    proof(cases "matches m (pf_rule2.get_match r) p")
    case True
    then show ?thesis unfolding PfRule using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
next
  case (Anchor r l)
  then show ?thesis
  proof(cases "matches m (anchor_rule2.get_match r) p")
    case True
    then show ?thesis using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
qed
qed
qed


fun first_quick_match :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> 'a pf_rule2 option" where
"first_quick_match [] _ _ = None"
|"first_quick_match (Option#ls) m p = first_quick_match ls m p"
|"first_quick_match ((PfRule r)#ls) m p =
(if (matches m (pf_rule2.get_match r) p) \<and> (pf_rule2.get_quick r)
then (Some r)
else first_quick_match ls m p)"
|"first_quick_match ((Anchor r b)#ls) m p =
(if (matches m (anchor_rule2.get_match r) p)
then first_quick_match (b@ls) m p
else first_quick_match ls m p)"

(*
lemma first_quick_match_decides:
  assumes "first_quick_match ls m p = Some r"
  shows "pf ls m p = (action_to_decision (pf_rule2.get_action r) <last matching decision>)"
*)

(*
lemma
  assumes "(filter l m p d) = d2 \<and> d \<noteq> d2"
  shows "\<forall> d. filter l m p d = d2"
*)

lemma pf_filter_equiv: "pf l1 m p = pf l2 m p \<longleftrightarrow> (\<forall> d. unwrap_decision (filter l1 m p d) = unwrap_decision (filter l2 m p d))"
proof
  assume "pf l1 m p = pf l2 m p"
  then show "(\<forall> d. unwrap_decision (filter l1 m p d) = unwrap_decision (filter l2 m p d))"
  proof(cases "pf l1 m p")
    case Accept
    then show ?thesis sorry
(* l1 and l2 decide accept somewhere \<rightarrow> will do so no matter the starting state *)
  next
    case Reject
    then show ?thesis sorry
(* l1 and l2 decide reject somewhere \<rightarrow> will do so no matter the starting state *)
  next
    case Undecided
    then show ?thesis sorry
(* l1 and l2 don't alter initial decision state at all *)
  qed
next
  assume "(\<forall> d. unwrap_decision (filter l1 m p d) = unwrap_decision (filter l2 m p d))"
  then show "pf l1 m p = pf l2 m p" unfolding pf_def by auto
qed

lemma filter_to_pf:
  assumes "\<forall> d. (filter l1 m p d = filter l2 m p d)"
  shows "pf l1 m p = pf l2 m p" unfolding pf_def using assms by auto

lemma filter_add_equiv_prefix :
  assumes "filter l1 m p d = filter l2 m p d"
          "\<And>d. filter l3 m p d = filter l4 m p d"
  shows "filter (l1@l3) m p d = filter (l2@l4) m p d"
proof -
    have "filter (l1@l3) m p d = filter l3 m p (filter l1 m p d)" by (simp add: filter_chain)
    moreover have "filter (l2@l4) m p d = filter l4 m p (filter l2 m p d)" by (simp add: filter_chain)
    ultimately show ?thesis using assms by auto
  qed

lemma filter_add_same_prefix :
  assumes "\<And>d. filter l1 m p d = filter l2 m p d"
  shows "filter (l@l1) m p d = filter (l@l2) m p d"
  by (metis assms filter_add_equiv_prefix)

lemma pf_add_same_prefix[intro]:
  assumes "pf l1 m p = pf l2 m p"
  shows "pf (l@l1) m p = pf (l@l2) m p"
  by (metis assms filter_chain pf_def pf_filter_equiv)

lemma pf_add_same_prefix'[intro]:
  assumes "pf l1 m p = pf l2 m p"
  shows "pf (l#l1) m p = pf (l#l2) m p"
  by (metis append_Cons append_Nil assms pf_add_same_prefix)


fun line_matches :: "'a line \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> bool" where
"line_matches Option _ _= False"
|"line_matches (PfRule r) m p = (matches m (pf_rule2.get_match r) p)"
|"line_matches (Anchor r l) m p = (matches m (anchor_rule2.get_match r) p)"

(*
lemma no_match_no_change : "\<forall> l\<in> set lines. \<not>(matches m
*)

lemma (* FIXME: this is not correct. *)
  assumes "(pf ls m p) = decision.Accept"
  shows "(\<exists> l\<in> set ls. (l = (PfRule r) \<and> (matches m (pf_rule2.get_match r) p) \<and> (pf_rule2.get_action r) = Match))"
proof(induction ls)
  case Nil
  then show ?case using assms sorry (*by blast*)
next
  case (Cons a ls)
  then show ?case sorry (*by blast*)
qed

lemma
  assumes "(pf ls m p) = decision.Undecided"
  shows "\<forall> d. filter ls m p d = d"
proof(induction ls)
  case Nil
  then show ?case sorry
next
  case (Cons a ls)
  then show ?case sorry
qed

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


lemma and_each_false[simp]:
  assumes "\<not>matches m e p"
  shows "filter (and_each e l) m p d = d"
proof(induction l)
case Nil
  then show ?case by (cases d, auto)
next
case (Cons a l)
  then show ?case using assms
    by (cases a; cases d; auto)
qed

lemma and_each_true[simp]:
  assumes "matches m e p"
  shows "filter (and_each e l) m p d = filter l m p d"
proof(induction l arbitrary:d)
case Nil
  then show ?case by (cases d, auto)
next
  case IH: (Cons a l)
  then show ?case
  proof(cases d)
    case (Final x1)
    then show ?thesis by auto
  next
    case (Preliminary x2)
    then show ?thesis unfolding Preliminary
      by (cases a,auto simp add: IH assms)
  qed
qed

lemma filter_foo: "filter [] m p (filter l m p (Preliminary d)) = filter l m p (Preliminary d)"
  by (metis append.right_neutral filter_chain)

lemma remove_anchors_preserves_semantics : "pf rules matcher packet = pf (remove_anchors rules) matcher packet"
proof(-)
  have "(filter rules matcher packet d = filter (remove_anchors rules) matcher packet d)" for d
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
    case Option
    then show ?thesis unfolding Option using IH by (cases d, auto)
  next
    case (PfRule r)
    then show ?thesis unfolding PfRule using IH by (cases d, auto)
  next
    case (Anchor r ls)
    then have "filter [(Anchor r ls)] matcher packet d =
               filter (and_each (anchor_rule2.get_match r) ls) matcher packet d"
    proof(cases "matches matcher (anchor_rule2.get_match r) packet")
      case True
      then have "filter (and_each (anchor_rule2.get_match r) ls) matcher packet (Preliminary x2)
                 = filter ls matcher packet (Preliminary x2)" by auto
      moreover have "PF.filter [Anchor r ls] matcher packet (Preliminary x2)
                 = filter ls matcher packet (Preliminary x2)" by (simp add: True filter_foo)
      ultimately show ?thesis unfolding Preliminary
        by simp
    next
      case False
      then show ?thesis unfolding Preliminary by auto
    qed

    then have "filter ([Anchor r ls] @ rules) matcher packet d = filter (and_each (get_match r) ls @ remove_anchors rules) matcher packet d"
      apply (rule filter_add_equiv_prefix)
      using IH by auto

    then show ?thesis unfolding Anchor
      by simp
  qed
  qed
qed
  then show ?thesis
    by (simp add: filter_to_pf)
qed


lemma and_each_preserves_length[simp] : "\<forall> mexp. length (and_each mexp rules) = length rules"
  by (induction rules, auto)

fun remove_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick [] = []"|
"remove_quick ((PfRule r)#ls) =
(if (get_quick r)
then
(remove_quick (and_each (MatchNot (pf_rule2.get_match r)) ls))@[PfRule (r\<lparr>get_quick := False\<rparr>)]
else
((PfRule r)#(remove_quick ls)))"|
"remove_quick (l#ls) = l#(remove_quick ls)"


fun remove_quick_alternate' :: "'a ruleset \<Rightarrow> 'a line list \<Rightarrow> 'a ruleset" where
"remove_quick_alternate' [] quick = quick"|
"remove_quick_alternate' ((PfRule r)#ls) quick =
(if (get_quick r)
then remove_quick_alternate' ls (PfRule (r\<lparr>get_quick := False\<rparr>)#quick)
else (PfRule r)#(remove_quick_alternate' ls quick))"|
"remove_quick_alternate' (l#ls) quick = l#(remove_quick_alternate' ls quick)"

fun remove_quick_alternate :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick_alternate rs = remove_quick_alternate' rs []"
(* remove_quick_alternate only works because we ignore any state altering rules.
If there would be rewriting/matching rules after the quick rule, that also match, they would take effect and might change the result.
With remove_quick, if something matches the quick rule, these rules explicitly cannot match, because they are ANDed with the negation of the quick rule's match condition.
TODO: check exact semantics of rewriting/matching rules (does only last rule or every matching rule get executed?)
*)

lemma remove_match_not:
  assumes "matches matcher matchexp p"
  shows "pf ((and_each (MatchNot matchexp) rules)@rules2) matcher p = pf rules2 matcher p"
proof(induction rules)
  case Nil
  then show ?case by auto
next
  case IH: (Cons a rules)
  then show ?case
  proof(cases a)
case Option
  then show ?thesis sorry
next
case (PfRule x2)
then show ?thesis sorry
next
  case (Anchor x31 x32)
  then show ?thesis sorry
qed

qed



(*
lemma remove_quick_preserves_semantics : "pf rules matcher packet = pf (remove_quick rules) matcher packet"
  apply(induction rules)
   apply(auto)
  apply(case_tac a)
    apply(auto)
*)

lemma remove_quick_preserves_semantics : "pf rules matcher packet = pf (remove_quick rules) matcher packet"
proof (induction rules)
  case Nil
  then show ?case sorry
next
  case (Cons a rules)
  then show ?case sorry
qed


(* induction on rules
case rule quick
true:
  case matches rule packet
    true:
      not matches rules packet
*)



(*
fun pf_to_simplefw :: "'a ruleset \<Rightarrow> 'a ruleset" where
"pf_to_simplefw rules = (map to_simple_match (reverse (normalize_firewall (remove_quick (remove_anchors rules)))))"
*)
end