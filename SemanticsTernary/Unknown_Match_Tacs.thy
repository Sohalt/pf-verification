theory Unknown_Match_Tacs
imports Matching_Ternary
begin

(* adapted from Iptables_Semantics.Unknown_Match_Tacs *)

section\<open>Approximate Matching Tactics\<close>
text\<open>in-doubt-tactics\<close>

fun in_doubt_allow :: "'packet unknown_match_tac" where
  "in_doubt_allow Pass _ = True" |
  "in_doubt_allow Block _ = False" |
  "in_doubt_allow _ _ = undefined"
  (*give it a simple_ruleset*)

fun in_doubt_deny :: "'packet unknown_match_tac" where
  "in_doubt_deny Pass _ = False" |
  "in_doubt_deny Block _ = True" |
  "in_doubt_deny _ _ = undefined"
  (*give it a simple_ruleset*)

lemma packet_independent_unknown_match_tacs:
    "packet_independent_\<alpha> in_doubt_allow"
    "packet_independent_\<alpha> in_doubt_deny"
  by(simp_all add: packet_independent_\<alpha>_def)


lemma Block_neq_Pass_unknown_match_tacs:
      "in_doubt_allow Block \<noteq> in_doubt_allow Pass"
      "in_doubt_deny Block \<noteq> in_doubt_deny Pass"
  by(simp_all add: fun_eq_iff)



(* use this more often to simplify existing proofs? *)
corollary matches_induction_case_MatchNot_in_doubt_allow:
      "\<forall> a. matches (\<beta>,in_doubt_allow) m' a p = matches (\<beta>,in_doubt_allow) m a p \<Longrightarrow>
      matches (\<beta>,in_doubt_allow) (MatchNot m') a p = matches (\<beta>,in_doubt_allow) (MatchNot m) a p"
  by(rule  matches_induction_case_MatchNot) (simp_all add: Block_neq_Pass_unknown_match_tacs packet_independent_unknown_match_tacs)
corollary matches_induction_case_MatchNot_in_doubt_deny:
      "\<forall> a. matches (\<beta>,in_doubt_deny) m' a p = matches (\<beta>,in_doubt_deny) m a p \<Longrightarrow>
      matches (\<beta>,in_doubt_deny) (MatchNot m') a p = matches (\<beta>,in_doubt_deny) (MatchNot m) a p"
  by(rule  matches_induction_case_MatchNot) (simp_all add: Block_neq_Pass_unknown_match_tacs packet_independent_unknown_match_tacs)

end