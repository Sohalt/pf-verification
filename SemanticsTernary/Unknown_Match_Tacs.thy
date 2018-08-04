theory Unknown_Match_Tacs
imports Matching_Ternary
begin

(* adapted from Iptables_Semantics.Unknown_Match_Tacs *)

section\<open>Approximate Matching Tactics\<close>
text\<open>in-doubt-tactics\<close>

fun in_doubt_allow :: "'packet unknown_match_tac" where
  "in_doubt_allow Pass _ _ = True" |
  "in_doubt_allow Block _ _ = False" |
  "in_doubt_allow action.Match Accept _ = True" |
  "in_doubt_allow action.Match Reject _ = False"

fun in_doubt_deny :: "'packet unknown_match_tac" where
  "in_doubt_deny Pass _ _ = False" |
  "in_doubt_deny Block _ _ = True" |
  "in_doubt_deny action.Match Accept _ = False" |
  "in_doubt_deny action.Match Reject _ = True"

lemma packet_independent_unknown_match_tacs:
    "packet_independent_\<alpha> in_doubt_allow"
    "packet_independent_\<alpha> in_doubt_deny"
  using in_doubt_allow.elims(3) packet_independent_\<alpha>_def apply fastforce
  using in_doubt_deny.elims(3) packet_independent_\<alpha>_def by fastforce


lemma Block_neq_Pass_unknown_match_tacs:
      "in_doubt_allow Block d \<noteq> in_doubt_allow Pass d"
      "in_doubt_deny Block d \<noteq> in_doubt_deny Pass d"
  by(simp_all add: fun_eq_iff)



(* use this more often to simplify existing proofs? *)
corollary matches_induction_case_MatchNot_in_doubt_allow:
      "\<forall> a. matches (\<beta>,in_doubt_allow) m' a d p = matches (\<beta>,in_doubt_allow) m a d p \<Longrightarrow>
      matches (\<beta>,in_doubt_allow) (MatchNot m') a d p = matches (\<beta>,in_doubt_allow) (MatchNot m) a d p"
  by(rule  matches_induction_case_MatchNot) (simp_all add: Block_neq_Pass_unknown_match_tacs packet_independent_unknown_match_tacs)

corollary matches_induction_case_MatchNot_in_doubt_deny:
      "\<forall> a. matches (\<beta>,in_doubt_deny) m' a d p = matches (\<beta>,in_doubt_deny) m a d p \<Longrightarrow>
      matches (\<beta>,in_doubt_deny) (MatchNot m') a d p = matches (\<beta>,in_doubt_deny) (MatchNot m) a d p"
  by(rule  matches_induction_case_MatchNot) (simp_all add: Block_neq_Pass_unknown_match_tacs packet_independent_unknown_match_tacs)

end