theory PF_Utils
  imports
PF_PF
begin
fun and_line :: "'a match_expr \<Rightarrow> 'a line \<Rightarrow> 'a line" where
"and_line m (PfRule r) =
(PfRule (r\<lparr>pf_rule.get_match := (MatchAnd m (pf_rule.get_match r))\<rparr>))" |
"and_line m (Anchor r l) =
(Anchor (r\<lparr>anchor_rule.get_match := (MatchAnd m (anchor_rule.get_match r))\<rparr>) l)"

case_of_simps and_line_cases:and_line.simps

fun and_each :: "'a match_expr \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
"and_each _ [] = []" |
"and_each m (l#ls) = (and_line m l)#(and_each m ls)"

lemma and_each_false[simp]:
  assumes "\<not>matches \<gamma> e p"
  shows "filter' (and_each e l) \<gamma> p d = d"
  using assms
  by (induction l) (auto split:line.splits decision_wrap.splits
                         simp:filter'_cases and_line_cases)

lemma and_each_true[simp]:
  assumes "matches \<gamma> e p"
  shows "filter' (and_each e l) \<gamma> p d = filter' l \<gamma> p d"
proof(induction l arbitrary:d)
  case Nil
  then show ?case by (cases d) auto
next
  case (Cons a l)
  then show ?case using assms
    by (cases d;cases a) auto
qed

lemma filter_add_equiv_prefix :
  assumes "filter' l1 m p d = filter' l2 m p d"
          "\<And>d. filter' l3 m p d = filter' l4 m p d"
  shows "filter' (l1@l3) m p d = filter' (l2@l4) m p d"
proof -
    have "filter' (l1@l3) m p d = filter' l3 m p (filter' l1 m p d)" by (simp add: filter_chain)
    moreover have "filter' (l2@l4) m p d = filter' l4 m p (filter' l2 m p d)" by (simp add: filter_chain)
    ultimately show ?thesis using assms by auto
qed

lemma filter_add_same_prefix :
  assumes "\<And>d. filter' l1 m p d = filter' l2 m p d"
  shows "filter' (l@l1) m p d = filter' (l@l2) m p d"
  by (metis assms filter_add_equiv_prefix)

lemma filter_cons_same_prefix :
  assumes "\<And>d. filter' l1 m p d = filter' l2 m p d"
  shows "filter' (l#l1) m p d = filter' (l#l2) m p d"
  by (metis append_Cons append_Nil assms filter_chain)

lemma remove_suffix[simp]:
  assumes "\<not>matches \<gamma> (pf_rule.get_match r) p"
  shows "filter' (l@[(PfRule r)]) \<gamma> p d = filter' l \<gamma> p d"
  using assms by (cases "filter' l \<gamma> p d") (simp add: filter_chain)+

end