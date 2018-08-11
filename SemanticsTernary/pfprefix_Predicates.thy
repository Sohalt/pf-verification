theory pfprefix_Predicates
imports
  "../pfprefix_Firewall_Common"
  "../pfprefix_Primitives"
  pfprefix_Matching_Ternary
begin
fun all_match :: "('a \<Rightarrow> bool) \<Rightarrow> 'a match_expr  \<Rightarrow> bool" where
"all_match _ MatchAny = True" |
"all_match P (MatchNot m) = all_match P m" |
"all_match P (MatchAnd m1 m2) = (all_match P m1 \<and> all_match P m2)" |
"all_match P (Match m) = P m"

definition no_ipv6 :: "common_primitive match_expr \<Rightarrow> bool" where
"no_ipv6 mexpr =
all_match (\<lambda>m. (case m of
(Src (Hostspec (Address (IPv6 _)))) \<Rightarrow> False
| (Dst (Address (IPv6 _))) \<Rightarrow> False
| _ \<Rightarrow> True)) mexpr"

definition no_af :: "common_primitive match_expr \<Rightarrow> bool" where
"no_af mexpr = all_match (\<lambda>m. (case m of (Address_Family _) \<Rightarrow> False)) mexpr"

definition good_match_expr :: "pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> bool" where
"good_match_expr ctx mexpr = all_match (good_primitive ctx) mexpr"

fun all_AnchorRules_P :: "('a anchor_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_AnchorRules_P P rs = (\<forall> l \<in> set rs. (case l of (Anchor r b) \<Rightarrow> P r \<and> all_AnchorRules_P P b | _ \<Rightarrow> True))"

fun all_AnchorRules_P' :: "('a anchor_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_AnchorRules_P' _ [] \<longleftrightarrow> True" |
"all_AnchorRules_P' P ((PfRule r)#ls) \<longleftrightarrow> all_AnchorRules_P' P ls" |
"all_AnchorRules_P' P ((Anchor r b)#ls) \<longleftrightarrow> P r \<and> all_AnchorRules_P' P b \<and> all_AnchorRules_P' P ls"

lemma "all_AnchorRules_P P l= all_AnchorRules_P' P l"
  by (induction P l rule: all_AnchorRules_P'.induct) auto

lemma all_AnchorRules_append[simp]:
  "all_AnchorRules_P P (xs @ ys) \<longleftrightarrow> all_AnchorRules_P P xs \<and> all_AnchorRules_P P ys"
  by (induction P xs rule: all_AnchorRules_P.induct) auto

definition no_anchors' :: "'a ruleset \<Rightarrow> bool" where
"no_anchors' rs = all_AnchorRules_P (\<lambda>r. False) rs"

lemma no_anchors_no_anchors'_eq:
 "no_anchors rs \<longleftrightarrow> no_anchors' rs"
  unfolding no_anchors'_def
  by (induction rs) (auto split:line.splits)


definition no_unknown_anchors :: "('a,'p) match_tac \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"no_unknown_anchors \<gamma> rs = all_AnchorRules_P
 (\<lambda>r. (\<forall> p. ternary_ternary_eval (map_match_tac (fst \<gamma>) p (anchor_rule.get_match r)) \<noteq> TernaryUnknown))
 rs"


fun all_PfRules_P :: "('a pf_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_PfRules_P P rs = (\<forall> l \<in> set rs. (case l of (PfRule r) \<Rightarrow> P r | (Anchor r b) \<Rightarrow> all_PfRules_P P b))"

fun all_PfRules_P' :: "('a pf_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_PfRules_P' _ [] \<longleftrightarrow> True" |
"all_PfRules_P' P ((PfRule r)#ls) \<longleftrightarrow> P r \<and> all_PfRules_P' P ls" |
"all_PfRules_P' P ((Anchor r b)#ls) \<longleftrightarrow> all_PfRules_P' P b \<and> all_PfRules_P' P ls"

lemma "all_PfRules_P P l= all_PfRules_P' P l"
  by (induction P l rule: all_PfRules_P'.induct) auto

lemma all_PfRules_append[simp]:
  "all_PfRules_P P (xs @ ys) \<longleftrightarrow> all_PfRules_P P xs \<and> all_PfRules_P P ys"
  by (induction P xs rule: all_PfRules_P.induct) auto

definition no_match_quick :: "'a ruleset \<Rightarrow> bool" where
"no_match_quick rs = all_PfRules_P (\<lambda>r. \<not>((pf_rule.get_action r) = ActionMatch \<and> pf_rule.get_quick r)) rs"


definition good_ruleset :: "pfcontext \<Rightarrow> common_primitive ruleset \<Rightarrow> bool" where
"good_ruleset ctx rs = (all_PfRules_P (\<lambda>r. good_match_expr ctx (pf_rule.get_match r)) rs \<and> all_AnchorRules_P (\<lambda>a. good_match_expr ctx (anchor_rule.get_match a)) rs)"
end