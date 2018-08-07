theory Pf_To_Simple_Firewall
imports PF
        Simple_Firewall.SimpleFw_Semantics
begin

fun and_line :: "'a match_expr \<Rightarrow> 'a line \<Rightarrow> 'a line" where
"and_line m (PfRule r) = (PfRule (r\<lparr>pf_rule.get_match := (MatchAnd m (pf_rule.get_match r))\<rparr>))"|
"and_line m (Anchor r l) = (Anchor (r\<lparr>anchor_rule.get_match := (MatchAnd m (anchor_rule.get_match r))\<rparr>) l)"

fun and_each :: "'a match_expr \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
"and_each _ [] = []"|
"and_each m (l#ls) = (and_line m l)#(and_each m ls)"

fun remove_anchors' :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_anchors' [] = []"|
"remove_anchors' ((Anchor r l) # rs) = (and_each (anchor_rule.get_match r) (remove_anchors' l)) @ (remove_anchors' rs)"|
"remove_anchors' (r#rs) = r#(remove_anchors' rs)"

fun remove_anchors :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_anchors [] = []"|
"remove_anchors ((Anchor r l) # rs) = (and_each (anchor_rule.get_match r) l) @ (remove_anchors rs)"|
"remove_anchors (r#rs) = r#(remove_anchors rs)"

fun count_anchors :: "'a ruleset \<Rightarrow> nat" where
"count_anchors [] = 0"
|"count_anchors ((Anchor r b)#l) = 1 + count_anchors b + count_anchors l"
|"count_anchors (_#l) = count_anchors l"

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
  case (3 r rs)
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

lemma remove_anchors'_ok : "no_anchors (remove_anchors' rules)"
proof(induction rules rule:remove_anchors'.induct)
case 1
then show ?case by simp
next
  case (2 r l rs)
  then have "count_anchors (remove_anchors' l) = 0" by (simp add:no_anchors_0_anchors)
  moreover have "count_anchors (remove_anchors' rs) = 0" using 2 by (simp add:no_anchors_0_anchors)
  ultimately have "count_anchors (remove_anchors' (Anchor r l # rs)) = 0" by simp
  then show ?case using no_anchors_0_anchors by blast
next
  case (3 v rs)
  then show ?case by simp
qed


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

lemma filter_cons_same_prefix :
  assumes "\<And>d. filter l1 m p d = filter l2 m p d"
  shows "filter (l#l1) m p d = filter (l#l2) m p d"
  by (metis append_Cons append_Nil assms filter_chain)

lemma and_each_false[simp]:
  assumes "\<not>matches \<gamma> e p"
  shows "filter (and_each e l) \<gamma> p d = d"
proof(induction l)
  case Nil
  then show ?case by (cases d, auto)
next
  case (Cons a l)
  then show ?case using assms
    by (cases a; cases d; auto)
qed

lemma and_each_true[simp]:
  assumes "matches \<gamma> e p"
  shows "filter (and_each e l) \<gamma> p d = filter l \<gamma> p d"
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

lemma filter_foo: "filter [] \<gamma> p (filter l \<gamma> p (Preliminary d)) = filter l \<gamma> p (Preliminary d)"
  by (metis append.right_neutral filter_chain)

lemma remove_anchors_preserves_semantics : "pf (remove_anchors rules) \<gamma> packet = pf rules \<gamma> packet"
proof(-)
  have "(filter rules \<gamma> packet d = filter (remove_anchors rules) \<gamma> packet d)" for d
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
    case (PfRule r)
    then show ?thesis unfolding PfRule using IH by (cases d, auto)
  next
    case (Anchor r ls)
    then have "filter [(Anchor r ls)] \<gamma> packet d =
               filter (and_each (anchor_rule.get_match r) ls) \<gamma> packet d"
    proof(cases "matches \<gamma> (anchor_rule.get_match r) packet")
      case True
      then have "filter (and_each (anchor_rule.get_match r) ls) \<gamma> packet (Preliminary x2)
                 = filter ls \<gamma> packet (Preliminary x2)" by auto
      moreover have "PF.filter [Anchor r ls] \<gamma> packet (Preliminary x2)
                 = filter ls \<gamma> packet (Preliminary x2)" by (simp add: True filter_foo)
      ultimately show ?thesis unfolding Preliminary
        by simp
    next
      case False
      then show ?thesis unfolding Preliminary by auto
    qed
    then have "filter ([Anchor r ls] @ rules) \<gamma> packet d = filter (and_each (get_match r) ls @ remove_anchors rules) \<gamma> packet d"
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

lemma remove_all_anchors_remove_anchors_idempotent:"pf (remove_all_anchors (remove_anchors rules)) \<gamma> packet = pf (remove_all_anchors rules) \<gamma> packet"
  by (metis le0 le_antisym no_anchors_0_anchors remove_all_anchors.simps remove_anchors_only_subtracts remove_anchors_preserves_semantics)

lemma remove_all_anchors_preserves_semantics : "pf rules \<gamma> packet = pf (remove_all_anchors rules) \<gamma> packet"
proof(induction rules rule: remove_all_anchors.induct)
  case (1 rules)
  then show ?case
  proof(cases "no_anchors rules")
    case True
    then show ?thesis by simp
  next
    case False
    then have "pf (remove_anchors rules) \<gamma> packet = pf (remove_all_anchors (remove_anchors rules)) \<gamma> packet" by (simp add: 1)
    moreover have "pf (remove_all_anchors (remove_anchors rules)) \<gamma> packet =  pf (remove_all_anchors rules) \<gamma> packet"
      by (meson remove_all_anchors_remove_anchors_idempotent)
    ultimately show ?thesis by (simp add: remove_anchors_preserves_semantics)
  qed
qed

lemma remove_anchors'_preserves_semantics:"pf (remove_anchors' rules) \<gamma> packet = pf rules \<gamma> packet"
proof(-)
  have "(filter rules \<gamma> packet d = filter (remove_anchors' rules) \<gamma> packet d)" for d
  proof(induction rules arbitrary: d rule:remove_anchors'.induct)
    case 1
    then show ?case by simp
  next
    case (2 r l rs)
    then show ?case
      proof(cases "matches \<gamma> (anchor_rule.get_match r) packet")
        case True
        then have "PF.filter (and_each (anchor_rule.get_match r) (remove_anchors' l)) \<gamma> packet d = PF.filter (remove_anchors' l) \<gamma> packet d" by simp
        then show ?thesis
        proof(cases d)
          case (Final x1)
          then show ?thesis by simp
        next
          case (Preliminary x2)
          then show ?thesis using True 2 by (auto simp add: filter_chain)
        qed
      next
        case False
        then have "PF.filter (and_each (anchor_rule.get_match r) (remove_anchors' l)) \<gamma> packet d = d" by simp
        then show ?thesis
        proof(cases d)
          case (Final x1)
          then show ?thesis by simp
        next
          case (Preliminary x2)
          then show ?thesis using False 2 by (auto simp add: filter_chain)
        qed
      qed
  next
    case (3 v rs)
    then show ?case apply simp
      by (meson filter_cons_same_prefix)
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


lemma and_each_preserves_no_quick:
  assumes "no_quick rs"
  shows "no_quick (and_each m rs)"
  using assms
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case by(cases a;simp)
qed


fun remove_single_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_single_quick [] = []"
|"remove_single_quick ((PfRule r)#ls) =
(if (get_quick r)
then
(and_each (MatchNot (pf_rule.get_match r)) ls)@[PfRule (r\<lparr>get_quick := False\<rparr>)]
else
((PfRule r)#(remove_single_quick ls)))"

fun count_quick :: "'a ruleset \<Rightarrow> nat" where
"count_quick [] = 0"
|"count_quick (l#ls) = (if (is_quick_rule l) then 1 else 0) + count_quick ls"

lemma no_quick_count_quick_0 : "count_quick rules = 0 \<longleftrightarrow> no_quick rules"
proof(induction rules)
case Nil
  then show ?case by simp
next
  case IH: (Cons a rules)
  then show ?case
  proof(cases a)
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
  case IH: (2 r ls)
  then show ?case
  proof(cases "get_quick r")
    case True
    then show ?thesis using IH by simp
  next
    case False
    then show ?thesis using IH by simp
  qed
next
  case (3 vb vc va)
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

lemma andeach_no_anchors:
  assumes "no_anchors rules"
  shows "no_anchors (and_each m rules)"
  using assms
proof(induction rules)
  case Nil
  then show ?case by simp
next
  case (Cons a rules)
  then show ?case by (cases a) auto
qed

lemma remove_single_quick_preserves_no_anchors:
  assumes "no_anchors rules"
  shows "no_anchors (remove_single_quick rules)"
  using assms
  by (induction rules rule:remove_single_quick.induct) (auto simp: andeach_no_anchors)

lemma remove_all_quick_ok:
  assumes "no_anchors rules"
  shows "no_quick (remove_all_quick rules)"
  using assms
  by (induction rules rule:remove_all_quick.induct) (metis remove_all_quick.elims remove_single_quick_preserves_no_anchors)

lemma remove_suffix[simp]:
  assumes "\<not>matches \<gamma> (pf_rule.get_match r) p"
  shows "filter (l@[(PfRule r)]) \<gamma> p d = filter l \<gamma> p d"
proof(cases "filter l \<gamma> p d")
  case (Final x1)
  then show ?thesis by (simp add: filter_chain)
next
  case (Preliminary x2)
  then show ?thesis using assms by (simp add:filter_chain)
qed

lemma remove_single_quick_preserves_semantics:
  assumes "no_anchors rules"
  shows "pf rules \<gamma> packet = pf (remove_single_quick rules) \<gamma> packet"
proof(-)
  from assms have "(unwrap_decision (filter rules \<gamma> packet d) = unwrap_decision (filter (remove_single_quick rules) \<gamma> packet d))" for d
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
        case (PfRule r)
        then show ?thesis
        proof(cases "get_quick r")
          case Quick:True
          then show ?thesis
          proof(cases "matches \<gamma> (pf_rule.get_match r) packet")
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

lemma remove_all_quick_preserves_semantics:
  assumes "no_anchors rules"
  shows "pf rules \<gamma> packet = pf (remove_all_quick rules) \<gamma> packet"
  using assms
proof(induction rules rule:remove_all_quick.induct)
  case (1 rules)
  then show ?case using remove_single_quick_preserves_no_anchors remove_single_quick_preserves_semantics unfolding pf_def
    apply (simp del: remove_all_quick.simps)
    sorry (* simplifier loops *)
qed

fun remove_quick' :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick' [] = []" |
"remove_quick' ((PfRule r)#ls) =
(if (get_quick r)
then (and_each (MatchNot (pf_rule.get_match r)) (remove_quick' ls))@[PfRule (r\<lparr>get_quick := False\<rparr>)]
else (PfRule r)#(remove_quick' ls))"

lemma remove_quick'_ok:
  assumes "no_anchors rules"
  shows "no_quick (remove_quick' rules)"
  using assms
proof(induction rules rule:remove_quick'.induct)
case 1
then show ?case by simp
next
  case (2 r ls)
  then show ?case by (auto simp: and_each_preserves_no_quick)
next
  case (3 vb vc va)
then show ?case by auto
qed

lemma remove_quick'_preserves_no_anchors :
  assumes "no_anchors rules"
  shows "no_anchors (remove_quick' rules)"
  using assms by(induction rules rule:remove_quick'.induct;auto simp:and_each_preserves_no_anchors)

lemma no_quick_preliminary:
  assumes "no_quick rules"
    and "no_anchors rules" (* not necessary but makes things easier *)
  shows "is_Preliminary (filter rules \<gamma> p (Preliminary d))"
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
      then show ?thesis unfolding PfRule using True nq na Cons by simp
    next
      case False
      then show ?thesis unfolding PfRule using Cons by auto
    qed
  next
    case (Anchor r b)
    then show ?thesis using Cons by auto
  qed
qed


lemma remove_quick'_preserves_semantics:
  assumes "no_anchors rules"
  shows "pf rules \<gamma> p = pf (remove_quick' rules) \<gamma> p"
proof(-)
  from assms have  "(unwrap_decision (filter rules \<gamma> p d) = unwrap_decision (filter (remove_quick' rules) \<gamma> p d))" for d
proof(induction rules arbitrary:d rule:remove_quick'.induct)
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

fun remove_matches :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_matches [] = []"
|"remove_matches ((PfRule r)#ls) = (if ((pf_rule.get_action r) = action.Match) then remove_matches ls else (PfRule r)#remove_matches ls)"
|"remove_matches (l#ls) = l#(remove_matches ls)"

lemma remove_matches_preserves_semantics:
  assumes "no_quick rules"
          "no_anchors rules"
    shows "pf rules matcher packet = pf (remove_matches rules) matcher packet"
proof(-)
  have "\<And>start_decision. filter rules matcher packet (Preliminary start_decision) = filter (remove_matches rules) matcher packet (Preliminary start_decision)"
  using assms
  by (induction rules arbitrary:start_decision rule: remove_matches.induct; simp)
  then show ?thesis by (simp add:pf_def)
qed

(*
fun pf_to_simplefw :: "'a ruleset \<Rightarrow> 'a ruleset" where
"pf_to_simplefw rules = (map to_simple_match (reverse (normalize_firewall (remove_quick (remove_anchors rules)))))"
*)
end
