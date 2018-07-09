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
"remove_anchors ((Anchor r l) # rs) = (and_each (anchor_rule2.get_match r) (*remove_anchors l*)l) @ (remove_anchors rs)"|
"remove_anchors (r#rs) = r#(remove_anchors rs)"

fun count_anchors :: "'a ruleset \<Rightarrow> nat" where
"count_anchors [] = 0"
|"count_anchors ((Anchor r b)#l) = 1 + count_anchors b + count_anchors l"
|"count_anchors (_#l) = count_anchors l"

abbreviation no_anchors :: "'a ruleset \<Rightarrow> bool" where
"no_anchors ls \<equiv> (\<forall>l \<in> set ls. \<not> is_Anchor l)"

lemma no_anchors_0_anchors: "count_anchors rules = 0 \<longleftrightarrow> no_anchors rules"
proof(induction rules)
  case Nil
  then show ?case by simp
next
  case (Cons a rules)
  then show ?case by (cases a,auto)
qed

lemma and_each_anchor_count_unchanged[simp]:
"count_anchors (and_each mexp rules) = count_anchors rules"
proof(induction rules)
  case Nil
  then show ?case by simp
next
  case (Cons a rules)
  then show ?case by (cases a, auto)
qed

lemma count_anchors_append[simp]:
"count_anchors (l1 @ l2) = count_anchors l1 + count_anchors l2"
proof(induction l1)
case Nil
then show ?case by simp
next
  case (Cons a l1)
  then show ?case by (cases a, auto)
qed

lemma remove_anchors_only_subtracts:
"count_anchors rules \<ge> count_anchors (remove_anchors rules)"
proof(induction rule: remove_anchors.induct)
  case 1
  then show ?case by simp
next
  case (2 r l rs)
  then show ?case by simp
next
  case ("3_1" rs)
  then show ?case by simp
next
  case ("3_2" v rs)
  then show ?case by simp
qed

lemma remove_anchors_only_subtracts':
  assumes "count_anchors rules > 0"
  shows "count_anchors rules > count_anchors (remove_anchors rules)"
proof(cases "count_anchors rules")
  case 0
  then show ?thesis using assms by auto
next
  case (Suc nat)
  then show ?thesis
  proof(induction rules)
    case Nil
    then show ?case by auto
  next
    case IH: (Cons a rules)
    then show ?case
    proof(cases a)
      case Option
      then show ?thesis using IH by auto
    next
      case (PfRule x2)
      then show ?thesis using IH by auto
    next
      case (Anchor x31 x32)
      then show ?thesis unfolding Anchor using remove_anchors_only_subtracts
        apply(auto)
        using le_imp_less_Suc by blast
    qed
  qed
qed

function remove_all_anchors :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_all_anchors rules = (if \<not>no_anchors rules then remove_all_anchors (remove_anchors rules) else rules)"
by pat_completeness auto

termination
  apply (relation "measure count_anchors")
   apply rule
  apply (subst in_measure)
  apply (rule remove_anchors_only_subtracts')
  using no_anchors_0_anchors by auto

lemma remove_all_anchors_ok : "no_anchors (remove_all_anchors rules)"
  sorry

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
  shows "pf l1 m p = pf l2 m p" unfolding pf_def using assms by simp

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


lemma and_each_preserves_length[simp] : "length (and_each mexp rules) = length rules"
  by (induction rules, auto)

fun remove_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick [] = []"|
"remove_quick ((PfRule r)#ls) =
(if (get_quick r)
then
(remove_quick (and_each (MatchNot (pf_rule2.get_match r)) ls))@[PfRule (r\<lparr>get_quick := False\<rparr>)]
else
((PfRule r)#(remove_quick ls)))"|
"remove_quick (Option#ls) = Option#(remove_quick ls)"
(* must not be called with anchors *)


fun remove_quick_alternate' :: "'a ruleset \<Rightarrow> 'a line list \<Rightarrow> 'a ruleset" where
"remove_quick_alternate' [] quick = quick"|
"remove_quick_alternate' ((PfRule r)#ls) quick =
(if (get_quick r)
then remove_quick_alternate' ls (PfRule (r\<lparr>get_quick := False\<rparr>)#quick)
else (PfRule r)#(remove_quick_alternate' ls quick))"|
"remove_quick_alternate' (l#ls) quick = l#(remove_quick_alternate' ls quick)"

definition remove_quick_alternate :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick_alternate rs = remove_quick_alternate' rs []"
(* remove_quick_alternate only works because we ignore any state altering rules.
If there would be rewriting/matching rules after the quick rule, that also match, they would take effect and might change the result.
With remove_quick, if something matches the quick rule, these rules explicitly cannot match, because they are ANDed with the negation of the quick rule's match condition.
TODO: check exact semantics of rewriting/matching rules (does only last rule or every matching rule get executed?)
*)

fun remove_single_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_single_quick [] = []"
|"remove_single_quick (Option#ls) = Option#(remove_single_quick ls)"
|"remove_single_quick ((PfRule r)#ls) =
(if (get_quick r)
then
(and_each (MatchNot (pf_rule2.get_match r)) ls)@[PfRule (r\<lparr>get_quick := False\<rparr>)]
else
((PfRule r)#(remove_single_quick ls)))"

fun count_quick :: "'a ruleset \<Rightarrow> nat" where
"count_quick [] = 0"
|"count_quick ((PfRule r)#ls) = (if (get_quick r) then 1 else 0) + count_quick ls"
|"count_quick (l#ls) = count_quick ls"

fun no_quick :: "'a ruleset \<Rightarrow> bool" where
"no_quick ls = (\<forall> l \<in> set ls. \<not>is_quick_rule l)"

lemma no_quick_count_quick_0 : "count_quick rules = 0 \<longleftrightarrow> no_quick rules"
proof(induction rules)
case Nil
  then show ?case by simp
next
  case IH: (Cons a rules)
  then show ?case
  proof(cases a)
case Option
  then show ?thesis using IH by auto
next
  case (PfRule r)
  then show ?thesis
  proof(cases "get_quick r")
    case True
    then show ?thesis unfolding PfRule using IH by simp
  next
    case False
    then show ?thesis unfolding PfRule using IH by simp
  qed
next
  case (Anchor x31 x32)
then show ?thesis using IH by auto
qed
qed

lemma and_each_quick_count_unchanged[simp]:
"count_quick (and_each mexp rules) = count_quick rules"
proof(induction rules)
  case Nil
  then show ?case by simp
next
  case (Cons a rules)
  then show ?case by (cases a, auto)
qed

lemma count_quick_append[simp]:
"count_quick (l1 @ l2) = count_quick l1 + count_quick l2"
proof(induction l1)
case Nil
then show ?case by simp
next
  case (Cons a l1)
  then show ?case by (cases a, auto)
qed

lemma remove_single_quick_only_subtracts:
  assumes "no_anchors rules"
  shows "count_quick rules \<ge> count_quick (remove_single_quick rules)"
  using assms
proof(induction rule:remove_single_quick.induct)
  case 1
  then show ?case by simp
next
  case (2 ls)
  then show ?case by simp
next
  case IH: (3 r ls)
  then show ?case
  proof(cases "get_quick r")
    case True
    then show ?thesis using IH by simp
  next
    case False
    then show ?thesis using IH by simp
  qed
next
  case (4 vb vc va)
  then show ?case by auto
qed


lemma remove_single_quick_only_subtracts':
  assumes "no_anchors rules"
          "count_quick rules > 0"
        shows "count_quick rules > count_quick (remove_single_quick rules)"
proof(cases "count_quick rules")
  case 0
  then show ?thesis using assms by auto
next
  case (Suc nat)
  then show ?thesis using \<open>no_anchors rules\<close>
  proof(induction rules)
    case Nil
    then show ?case by auto
  next
    case IH: (Cons a rules)
    then show ?case
    proof(cases a)
      case Option
      then show ?thesis using IH by auto
    next
      case (PfRule x2)
      then show ?thesis using IH by auto
    next
      case (Anchor x31 x32)
      then show ?thesis using IH by auto
    qed
  qed
qed


function remove_all_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_all_quick rules = (if no_anchors rules then (if no_quick rules then rules else (remove_all_quick (remove_single_quick rules))) else undefined)"
  by pat_completeness auto

termination remove_all_quick
  apply (relation "measure count_quick")
   apply rule
  apply (subst in_measure)
  apply (rule remove_single_quick_only_subtracts')
  using no_quick_count_quick_0 by auto


lemma pf_option_prefix[simp]:
"pf (Option#l) m p = pf l m p"
proof(induction l)
  case Nil
  then show ?case unfolding pf_def by simp
next
  case (Cons a l)
  then show ?case unfolding pf_def by simp
qed

lemma pf_pfrule_prefix[simp]:
  assumes "\<not>matches m (pf_rule2.get_match r) p"
  shows "pf ((PfRule r)#l) m p = pf l m p"
proof(induction l)
case Nil
then show ?case unfolding pf_def using assms by simp
next
  case (Cons a l)
  then show ?case unfolding pf_def using assms by simp
qed

lemma pf_anchor_prefix[simp]:
  assumes "\<not>matches m (anchor_rule2.get_match r) p"
  shows "pf ((Anchor r b)#l) m p = pf l m p"
proof(induction l)
  case Nil
  then show ?case unfolding pf_def using assms by simp
next
  case (Cons a l)
  then show ?case unfolding pf_def using assms by simp
qed

lemma remove_match_not[simp]:
  assumes "matches matcher matchexp p"
  shows "pf ((and_each (MatchNot matchexp) rules)@rules2) matcher p = pf rules2 matcher p"
proof(induction rules)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a rules)
  then show ?case
  proof(cases a)
    case Option
    then show ?thesis unfolding Option by (auto simp: IH)
  next
    case (PfRule x2)
    then show ?thesis unfolding PfRule using assms IH by simp
  next
    case (Anchor x31 x32)
    then show ?thesis unfolding Anchor using assms IH by simp
  qed
qed

lemma quick_rule_decides[simp]:
  assumes "matches matcher (pf_rule2.get_match r) packet"
          "get_quick r"
  shows "pf (PfRule r # ls) matcher packet = action_to_decision (pf_rule2.get_action r) decision.Undecided"
  unfolding pf_def using assms by auto


fun line_matches :: "'a line \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> bool" where
"line_matches Option _ _= False"
|"line_matches (PfRule r) m p = (matches m (pf_rule2.get_match r) p)"
|"line_matches (Anchor r l) m p = (matches m (anchor_rule2.get_match r) p)"

fun no_line_matches :: "'a line list \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> bool" where
"no_line_matches [] m p = True"
|"no_line_matches (l#ls) m p = (\<not>line_matches l m p \<and> no_line_matches ls m p)"

lemma remove_suffix[simp]:
  assumes "\<not>matches m (pf_rule2.get_match r) p"
  shows "filter (l@[(PfRule r)]) m p d = filter l m p d"
proof(cases "filter l m p d")
  case (Final x1)
  then show ?thesis by (simp add: filter_chain)
next
  case (Preliminary x2)
  then show ?thesis using assms by (simp add:filter_chain)
qed

lemma remove_single_quick_preserves_semantics:
  assumes "no_anchors rules"
  shows "pf rules matcher packet = pf (remove_single_quick rules) matcher packet"
proof(-)
  from assms have "(unwrap_decision (filter rules matcher packet d) = unwrap_decision (filter (remove_single_quick rules) matcher packet d))" for d
  proof(induction rules arbitrary: d)
    case Nil
    then show ?case by simp
  next
    case IH: (Cons a rules)
    then show ?case
    proof(cases d)
      case (Final x1)
      then show ?thesis by simp
    next
      case (Preliminary x2)
      then show ?thesis
      proof(cases a)
        case Option
        then show ?thesis unfolding Option using Preliminary IH by auto
      next
        case (PfRule r)
        then show ?thesis
        proof(cases "get_quick r")
          case Quick:True
          then show ?thesis
          proof(cases "matches matcher (pf_rule2.get_match r) packet")
            case True
            then show ?thesis unfolding PfRule Preliminary using Quick by (simp add:filter_chain)
          next
            case False
            then show ?thesis unfolding PfRule Preliminary using Quick by auto
          qed
        next
          case False
          then show ?thesis unfolding PfRule using IH by (cases d, auto)
        qed
      next
        case (Anchor x31 x32)
        then show ?thesis using IH by auto
      qed
    qed
  qed
  then show ?thesis by (simp add: pf_def)
qed


lemma remove_quick_only_restricts_matches:
  assumes "no_line_matches lines m p"
  shows "no_line_matches (remove_quick lines) m p"
proof(induction lines)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a lines)
  then show ?case
  proof(cases a)
    case Option
    then show ?thesis using IH assms by auto
  next
    case (PfRule x2)
    then show ?thesis using IH sorry
  next
    case (Anchor x31 x32)
    then show ?thesis sorry
  qed
qed


fun is_preliminary :: "decision_wrap \<Rightarrow> bool" where
"is_preliminary (Preliminary d) = True"
|"is_preliminary (Final d) = False"


lemma remove_quick_ok:
  assumes "no_anchors rules"
  shows "no_quick (remove_quick rules)"
proof(induction rules)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a rules)
  then show ?case
(*
  proof(cases "is_quick_rule a")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
*)
  proof(cases a)
    case Option
    then show ?thesis using IH by auto
  next
    case (PfRule r)
    then show ?thesis unfolding PfRule using IH
      apply(auto) (* and_each doesn't affect quick: how do I write down that some function doesn't touch record fields? *)
      sorry
  next
    case (Anchor x31 x32)
    then show ?thesis sorry (* contr assms *)
  qed
qed


lemma remove_quick_no_final_decision:
  assumes "no_anchors rules"
  shows "is_preliminary (filter (remove_quick rules) matcher packet (Preliminary d))"
proof(induction rules arbitrary: d)
  case Nil
  then show ?case by simp
next
  case IH: (Cons a rules)
  then show ?case
  proof(cases a)
    case Option
    then show ?thesis using IH by simp
  next
    case (PfRule r)
    then show ?thesis
    proof(cases "pf_rule2.get_quick r")
      case True
      then show ?thesis unfolding PfRule using IH
        sorry
    next
      case False
      then show ?thesis unfolding PfRule using IH by auto
    qed
  next
    case (Anchor x31 x32)
    then show ?thesis sorry (* assms contradiction *)
  qed
qed

(*
proof (induction arbitrary: d rule:remove_quick.induct)
  case 1
  then show ?case by simp
next
  case (2 r ls)
  then show ?case
  proof(cases "get_quick r")
    case Quick: True
    then show ?thesis sorry
  next
    case NotQuick: False
    then show ?thesis using 2
    proof(cases "matches matcher (pf_rule2.get_match r) packet")
      case True
      then show ?thesis using 2 NotQuick by simp
    next
      case False
      then show ?thesis using 2 NotQuick by simp
    qed
  qed
next
  case (3 ls)
  then show ?case by simp
next
  case (4 vb vc va)
  then show ?case sorry (* contradiction in assumption *)
qed
*)

lemma remove_quick_preserves_semantics : "pf rules matcher packet = pf (remove_quick rules) matcher packet"
proof (induction rules rule:remove_quick.induct)
  case 1
  then show ?case by simp
next
  case (2 r ls)
  then show ?case
  proof(cases "get_quick r")
    case t: True
    then show ?thesis
    proof(cases "matches matcher (pf_rule2.get_match r) packet")
      case True
      then show ?thesis using t 2
        apply auto
        sorry
    next
      case False
      then show ?thesis sorry
    qed
  next
    case False
    then show ?thesis using 2 by auto
  qed
next
  case ("3" ls)
  then show ?case by simp
next
  case ("4" r b ls)
  then show ?case sorry
qed


(*
fun pf_to_simplefw :: "'a ruleset \<Rightarrow> 'a ruleset" where
"pf_to_simplefw rules = (map to_simple_match (reverse (normalize_firewall (remove_quick (remove_anchors rules)))))"
*)
end