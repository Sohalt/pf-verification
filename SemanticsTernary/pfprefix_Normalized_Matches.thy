theory pfprefix_Normalized_Matches
  imports pfprefix_Semantics_Ternary
          pfprefix_Fixed_Action
begin
(* adapted from Iptables_Semantics.Normalized_Matches *)

text\<open>simplify a match expression. The output is a list of match expressions, the semantics is @{text "\<or>"} of the list elements.\<close>
fun normalize_match :: "'a match_expr \<Rightarrow> 'a match_expr list" where
  "normalize_match (MatchAny) = [MatchAny]" |
  "normalize_match (Match m) = [Match m]" |
  "normalize_match (MatchAnd m1 m2) = [MatchAnd x y. x <- normalize_match m1, y <- normalize_match m2]" |
  "normalize_match (MatchNot (MatchAnd m1 m2)) = normalize_match (MatchNot m1) @ normalize_match (MatchNot m2)" | (*DeMorgan*)
  "normalize_match (MatchNot (MatchNot m)) = normalize_match m" | (*idem*)
  "normalize_match (MatchNot (MatchAny)) = []" | (*false*)
  "normalize_match (MatchNot (Match m)) = [MatchNot (Match m)]"

fun normalized_nnf_match :: "'a match_expr \<Rightarrow> bool" where
  "normalized_nnf_match MatchAny = True" |
  "normalized_nnf_match (Match _ ) = True" |
  "normalized_nnf_match (MatchNot (Match _)) = True" |
  "normalized_nnf_match (MatchAnd m1 m2) = ((normalized_nnf_match m1) \<and> (normalized_nnf_match m2))" |
  "normalized_nnf_match _ = False"


text\<open>Essentially, @{term normalized_nnf_match} checks for a negation normal form: Only AND is at toplevel, negation only occurs in front of literals.
 Since @{typ "'a match_expr"} does not support OR, the result is in conjunction normal form.
 Applying @{const normalize_match}, the result is a list. Essentially, this is the disjunctive normal form.\<close>

lemma normalize_match_already_normalized: "normalized_nnf_match m \<Longrightarrow> normalize_match m = [m]"
  by(induction m rule: normalize_match.induct) (simp)+

lemma normalized_nnf_match_normalize_match: "\<forall> m' \<in> set (normalize_match m). normalized_nnf_match m'"
  proof(induction m arbitrary: rule: normalize_match.induct)
  case 4 thus ?case by fastforce
  qed (simp_all)

lemma normalized_nnf_match_MatchNot_D: "normalized_nnf_match (MatchNot m) \<Longrightarrow> normalized_nnf_match m"
  by(induction m) (simp_all)

text\<open>Example\<close>
lemma "normalize_match (MatchNot (MatchAnd (Match ip_src) (Match tcp))) = [MatchNot (Match ip_src), MatchNot (Match tcp)]" by simp

lemma match_list_normalize_match: "match_list \<gamma> [m] a d p \<longleftrightarrow> match_list \<gamma> (normalize_match m) a d p"
  proof(induction m rule:normalize_match.induct)
  case 1 thus ?case by(simp add: match_list_singleton)
  next
  case 2 thus ?case by(simp add: match_list_singleton)
  next
  case (3 m1 m2) thus ?case 
    apply(simp_all add: match_list_singleton del: match_list.simps(2))
    apply(case_tac "matches \<gamma> m1 a d p")
     apply(rule matches_list_And_concat)
      apply(simp)
     apply(case_tac "(normalize_match m1)")
      apply simp
     apply (auto)[1]
    apply(simp add: bunch_of_lemmata_about_matches match_list_helper)
    done
  next
  case 4 thus ?case 
    apply(simp_all add: match_list_singleton del: match_list.simps(2))
    apply(simp add: match_list_append)
    apply(safe)
        apply(simp_all add: matches_DeMorgan)
    done
  next 
  case 5 thus ?case 
    by(simp add: match_list_singleton bunch_of_lemmata_about_matches)
  next
  case 6 thus ?case 
    by(simp add: match_list_singleton bunch_of_lemmata_about_matches)
  next
  case 7 thus ?case by(simp add: match_list_singleton)
qed
  
thm match_list_normalize_match[simplified match_list_singleton]

theorem normalize_match_correct: 
  shows "pf_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) (normalize_match m)) \<gamma> p =
 pf_approx [PfRule \<lparr> get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>] \<gamma> p"
proof(-)
  have "\<And>d. filter_approx' (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) (normalize_match m)) \<gamma> p d =
 filter_approx' [PfRule \<lparr> get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>] \<gamma> p d"
    using match_list_semantics[of _ "[m]", simplified] match_list_normalize_match
    by (smt list.map(1) list.simps(9) map_eq_conv match_list_semantics)
  then show ?thesis by (simp add:filter_approx'_to_pf_approx)
qed
end