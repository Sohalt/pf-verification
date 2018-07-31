theory Firewall_Common
  imports 
"HOL-Library.Simps_Case_Conv"
begin
(* Block return semantically equal to Block (without return)*)
datatype action = Pass | Match | Block

(* Matching Algebra taken from Iptaples_Semantics*)
datatype 'a match_expr = Match 'a
                       | MatchNot "'a match_expr"
                       | MatchAnd "'a match_expr" "'a match_expr"
                       | MatchAny

definition MatchNone :: "'a match_expr" where
"MatchNone = MatchNot MatchAny"

definition MatchOr :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" where
  "MatchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2))"


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

datatype decision =
  Accept
  | Reject

fun action_to_decision :: "action \<Rightarrow> decision \<Rightarrow> decision" where
"action_to_decision Pass _ = Accept"|
"action_to_decision Block _ = Reject"|
"action_to_decision action.Match d = d"

case_of_simps action_to_decision_cases: action_to_decision.simps

datatype decision_wrap =
  Final decision
  | Preliminary decision

fun unwrap_decision :: "decision_wrap \<Rightarrow> decision" where
"unwrap_decision (Final d) = d"
|"unwrap_decision (Preliminary d) = d"

case_of_simps unwrap_decision_cases: unwrap_decision.simps


text\<open>Structural properties about match expressions\<close>
  fun has_primitive :: "'a match_expr \<Rightarrow> bool" where
    "has_primitive MatchAny = False" |
    "has_primitive (Match a) = True" |
    "has_primitive (MatchNot m) = has_primitive m" |
    "has_primitive (MatchAnd m1 m2) = (has_primitive m1 \<or> has_primitive m2)"

  text\<open>Is a match expression equal to the @{const MatchAny} expression?
        Only applicable if no primitives are in the expression.\<close>
  fun matcheq_matchAny :: "'a match_expr \<Rightarrow> bool" where
    "matcheq_matchAny MatchAny \<longleftrightarrow> True" |
    "matcheq_matchAny (MatchNot m) \<longleftrightarrow> \<not> (matcheq_matchAny m)" |
    "matcheq_matchAny (MatchAnd m1 m2) \<longleftrightarrow> matcheq_matchAny m1 \<and> matcheq_matchAny m2" |
    "matcheq_matchAny (Match _) = undefined"

  fun matcheq_matchNone :: "'a match_expr \<Rightarrow> bool" where
    "matcheq_matchNone MatchAny = False" |
    "matcheq_matchNone (Match _) = False" |
    "matcheq_matchNone (MatchNot MatchAny) = True" |
    "matcheq_matchNone (MatchNot (Match _)) = False" |
    "matcheq_matchNone (MatchNot (MatchNot m)) = matcheq_matchNone m" |
    "matcheq_matchNone (MatchNot (MatchAnd m1 m2)) \<longleftrightarrow> matcheq_matchNone (MatchNot m1) \<and> matcheq_matchNone (MatchNot m2)" |
    "matcheq_matchNone (MatchAnd m1 m2) \<longleftrightarrow>  matcheq_matchNone m1 \<or> matcheq_matchNone m2"
  
  lemma matachAny_matchNone: "\<not> has_primitive m \<Longrightarrow> matcheq_matchAny m \<longleftrightarrow> \<not> matcheq_matchNone m"
    by(induction m rule: matcheq_matchNone.induct)(simp_all)
  
  lemma matcheq_matchNone_no_primitive: "\<not> has_primitive m \<Longrightarrow> matcheq_matchNone (MatchNot m) \<longleftrightarrow> \<not> matcheq_matchNone m"
    by(induction m rule: matcheq_matchNone.induct) (simp_all)



end