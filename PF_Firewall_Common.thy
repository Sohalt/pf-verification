theory PF_Firewall_Common
  imports 
"HOL-Library.Simps_Case_Conv"
Iptables_Semantics.Firewall_Common
PF_Primitives
begin
(* Block return semantically equal to Block (without return)*)
datatype action = Pass | ActionMatch | Block

definition MatchNone :: "'a match_expr" where
"MatchNone = MatchNot MatchAny"

record 'a pf_rule =
  get_action :: action
  get_quick :: bool
  get_match :: "'a match_expr"

record 'a anchor_rule =
  get_match :: "'a match_expr"

datatype 'a line =
  PfRule "'a pf_rule"
  | is_Anchor: Anchor "'a anchor_rule" "'a line list"

quickcheck_generator line constructors: PfRule

type_synonym 'a ruleset = "'a line list"

abbreviation no_anchors :: "'a ruleset \<Rightarrow> bool" where
"no_anchors ls \<equiv> (\<forall>l \<in> set ls. \<not> is_Anchor l)"

fun is_quick_rule :: "'a line \<Rightarrow> bool" where
"is_quick_rule (PfRule r) = (get_quick r)"
| "is_quick_rule _ = False"

case_of_simps is_quick_rule_cases:is_quick_rule.simps

abbreviation no_quick :: "'a ruleset \<Rightarrow> bool" where
"no_quick ls \<equiv> (\<forall> l \<in> set ls. \<not>is_quick_rule l)"

abbreviation no_match :: "'a ruleset \<Rightarrow> bool" where
"no_match ls \<equiv> (\<forall> l \<in> set ls. (case l of (PfRule r) \<Rightarrow> (pf_rule.get_action r) \<noteq> ActionMatch
                                          | _ \<Rightarrow> True))"

definition simple_ruleset :: "'a ruleset \<Rightarrow> bool" where
"simple_ruleset rs \<equiv> (no_anchors rs \<and> no_quick rs \<and> no_match rs)"

datatype decision =
  Accept
  | Reject

fun action_to_decision :: "action \<Rightarrow> decision \<Rightarrow> decision" where
"action_to_decision Pass _ = Accept"|
"action_to_decision Block _ = Reject"|
"action_to_decision ActionMatch d = d"

case_of_simps action_to_decision_cases: action_to_decision.simps

datatype decision_wrap =
  Final decision
  | is_Preliminary: Preliminary decision

fun unwrap_decision :: "decision_wrap \<Rightarrow> decision" where
"unwrap_decision (Final d) = d"
|"unwrap_decision (Preliminary d) = d"

case_of_simps unwrap_decision_cases: unwrap_decision.simps

end