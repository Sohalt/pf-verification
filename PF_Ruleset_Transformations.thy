theory PF_Ruleset_Transformations
  imports
PF_PF
PF_Utils   
Simple_Firewall.SimpleFw_Semantics
begin

(* remove anchors *)
fun remove_anchors :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_anchors [] = []" |
"remove_anchors ((Anchor r l) # rs) =
(and_each (anchor_rule.get_match r) (remove_anchors l)) @ (remove_anchors rs)" |
"remove_anchors (r#rs) = r#(remove_anchors rs)"

fun count_anchors :: "'a ruleset \<Rightarrow> nat" where
"count_anchors [] = 0"
|"count_anchors ((Anchor r b)#l) = 1 + count_anchors b + count_anchors l"
|"count_anchors (_#l) = count_anchors l"

case_of_simps count_anchors_cases:count_anchors.simps

lemma no_anchors_0_anchors: "count_anchors rs = 0 \<longleftrightarrow> no_anchors rs"
  by (induction rs) (simp split:line.splits add:count_anchors_cases)+

lemma and_each_anchor_count_unchanged[simp]:
"count_anchors (and_each mexp rs) = count_anchors rs"
  by (induction rs) (simp split:line.splits add:count_anchors_cases)+

lemma count_anchors_append[simp]:
"count_anchors (l1 @ l2) = count_anchors l1 + count_anchors l2"
  by (induction l1) (simp split:line.splits add:count_anchors_cases)+


lemma remove_anchors_ok : "no_anchors (remove_anchors rules)"
proof(induction rules rule:remove_anchors.induct)
  case (2 r l rs)
  then have "count_anchors (remove_anchors l) = 0" by (simp add:no_anchors_0_anchors)
  moreover have "count_anchors (remove_anchors rs) = 0" using 2 by (simp add:no_anchors_0_anchors)
  ultimately have "count_anchors (remove_anchors (Anchor r l # rs)) = 0" by simp
  then show ?case using no_anchors_0_anchors by blast
qed simp+


lemma remove_anchors_preserves_semantics:
"pf (remove_anchors rules) \<gamma> packet = pf rules \<gamma> packet"
proof(-)
  have "(filter' rules \<gamma> packet d = filter' (remove_anchors rules) \<gamma> packet d)" for d
  proof(induction rules arbitrary: d rule:remove_anchors.induct)
    case 1
    then show ?case by simp
  next
    case (2 r l rs)
    then show ?case
      by (cases "matches \<gamma> (anchor_rule.get_match r) packet";cases d) (auto simp add: filter_chain)
  next
    case (3 v rs)
    then show ?case by (cases d) auto
  qed
  then show ?thesis by (simp add: filter_to_pf)
qed

lemma and_each_preserves_no_anchors:
  assumes "no_anchors rs"
    shows "no_anchors (and_each m rs)"
    using assms
proof(induction m rs rule:and_each.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 m l ls)
  then show ?case by (cases l;simp)
qed

(* remove quick rules *)

fun remove_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick [] = []" |
"remove_quick ((PfRule r)#ls) =
(if (get_quick r)
  then (and_each (MatchNot (pf_rule.get_match r)) (remove_quick ls)) @ [PfRule (r\<lparr>get_quick := False\<rparr>)]
  else (PfRule r)#(remove_quick ls))"

fun count_quick :: "'a ruleset \<Rightarrow> nat" where
"count_quick [] = 0"
|"count_quick (l#ls) = (if (is_quick_rule l) then 1 else 0) + count_quick ls"

lemma no_quick_count_quick_0 : "count_quick rs = 0 \<longleftrightarrow> no_quick rs"
  by (induction rs) (auto split:line.splits simp:is_quick_rule_cases)

lemma and_each_quick_count_unchanged[simp]:
"count_quick (and_each mexp rs) = count_quick rs"
  by (induction rs) (auto split:line.splits simp:is_quick_rule_cases)

lemma count_quick_append[simp]:
"count_quick (l1 @ l2) = count_quick l1 + count_quick l2"
  by (induction l1) (auto split:line.splits)

lemma and_each_preserves_no_quick:
  assumes "no_quick rs"
    shows "no_quick (and_each m rs)"
  using assms
  by (induction rs) (auto split:line.splits simp:is_quick_rule_cases)

lemma remove_quick_ok:
  assumes "no_anchors rules"
  shows "no_quick (remove_quick rules)"
  using assms
  by (induction rules rule:remove_quick.induct)
     (auto simp: and_each_preserves_no_quick)

lemma remove_quick_preserves_no_anchors :
  assumes "no_anchors rules"
  shows "no_anchors (remove_quick rules)"
  using assms by(induction rules rule:remove_quick.induct)
                (auto simp:and_each_preserves_no_anchors)

lemma no_quick_preliminary:
  assumes "no_quick rules"
      and "no_anchors rules" (* not necessary but makes things easier *)
    shows "is_Preliminary (filter' rules \<gamma> p (Preliminary d))"
  using assms
proof(induction rules arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons a rules)
  then show ?case
  proof(cases a)
    case (PfRule r)
    then show ?thesis
    proof(cases "matches \<gamma> (pf_rule.get_match r) p")
      case True
      have nq:"no_quick rules" using Cons by simp
      have na:"no_anchors rules" using Cons by simp
      have "\<not>get_quick r" using Cons PfRule by auto
      then show ?thesis using True nq na Cons PfRule by simp
    next
      case False
      then show ?thesis using PfRule Cons by auto
    qed
  next
    case (Anchor r b)
    then show ?thesis using Cons by auto
  qed
qed


lemma remove_quick_preserves_semantics:
  assumes "no_anchors rules"
  shows "pf rules \<gamma> p = pf (remove_quick rules) \<gamma> p"
proof(-)
  have "(unwrap_decision (filter' rules \<gamma> p d) = unwrap_decision (filter' (remove_quick rules) \<gamma> p d))" for d
    using assms
  proof(induction rules arbitrary:d rule:remove_quick.induct)
  case 1
  then show ?case by simp
  next
    case (2 r ls)
    then show ?case
    proof(cases d)
      case (Final x1)
      then show ?thesis by auto
    next
      case (Preliminary x2)
      then show ?thesis
      proof(cases "get_quick r")
        case quick:True
        then show ?thesis
        proof(cases "matches \<gamma> (pf_rule.get_match r) p")
          case match:True
          then show ?thesis using 2 Preliminary quick by (simp add:filter_chain)
        next
          case nomatch:False
          then show ?thesis using 2 Preliminary by simp
        qed
      next
        case False
        then show ?thesis using 2 Preliminary by auto
      qed
    qed
  next
  case (3 vb vc va)
    then show ?case by auto
  qed
  then show ?thesis by (simp add:pf_def)
qed


(* remove matches *)

fun remove_matches :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_matches [] = []" |
"remove_matches ((PfRule r)#ls) =
(if ((pf_rule.get_action r) = ActionMatch)
  then remove_matches ls
  else (PfRule r)#remove_matches ls)" |
"remove_matches (l#ls) = l#(remove_matches ls)"

lemma remove_matches_ok:
"no_match (remove_matches rs)"
  by(induction rs rule:remove_matches.induct) auto

lemma remove_matches_preserves_semantics:
  assumes "no_quick rs"
      and "no_anchors rs"
    shows "pf rs \<gamma> p = pf (remove_matches rs) \<gamma> p"
proof(-)
  have "\<And>d. filter' rs \<gamma> p (Preliminary d) = filter' (remove_matches rs) \<gamma> p (Preliminary d)"
  using assms
    by (induction rs rule: remove_matches.induct) simp+
  then show ?thesis by (simp add:pf_def)
qed

end
