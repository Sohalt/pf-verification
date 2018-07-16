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
by (induction rules rule: remove_all_anchors.induct) (metis remove_all_anchors.elims)

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




fun remove_single_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_single_quick [] = []"
|"remove_single_quick (Option#ls) = Option#(remove_single_quick ls)"
|"remove_single_quick ((PfRule r)#ls) =
(if (get_quick r)
then
(and_each (MatchNot (pf_rule2.get_match r)) ls)@[PfRule (r\<lparr>get_quick := False\<rparr>)]
else
((PfRule r)#(remove_single_quick ls)))"

fun is_quick_rule :: "'a line \<Rightarrow> bool" where
"is_quick_rule (PfRule r) = (get_quick r)"
| "is_quick_rule _ = False"

fun count_quick :: "'a ruleset \<Rightarrow> nat" where
"count_quick [] = 0"
|"count_quick (l#ls) = (if (is_quick_rule l) then 1 else 0) + count_quick ls"

abbreviation no_quick :: "'a ruleset \<Rightarrow> bool" where
"no_quick ls \<equiv> (\<forall> l \<in> set ls. \<not>is_quick_rule l)"

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

lemma remove_all_quick_ok:
  assumes "no_anchors rules"
  shows "no_quick (remove_all_quick rules)"
  sorry

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

fun remove_matches :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_matches [] = []"
|"remove_matches ((PfRule r)#ls) = (if ((pf_rule2.get_action r) = action.Match) then remove_matches ls else (PfRule r)#remove_matches ls)"
|"remove_matches (l#ls) = l#(remove_matches ls)"

lemma remove_matches_ok:
  assumes "no_quick rules"
          "no_anchors rules"
  shows "filter rules matcher packet (Preliminary start_decision) = filter (remove_matches rules) matcher packet (Preliminary start_decision)"
  using assms
  by (induction rules arbitrary:start_decision rule: remove_matches.induct; simp)
(*
fun pf_to_simplefw :: "'a ruleset \<Rightarrow> 'a ruleset" where
"pf_to_simplefw rules = (map to_simple_match (reverse (normalize_firewall (remove_quick (remove_anchors rules)))))"
*)
end