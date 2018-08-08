theory pfprefix_Fixed_Action
  imports pfprefix_Semantics_Ternary
          Iptables_Semantics.List_Misc
begin
(* adapted from Iptables_Semantics.Fixed_Action *)

section\<open>Fixed Action\<close>

text\<open>If firewall rules have the same action, we can focus on the matching only.\<close>

lemma [simp]:
  assumes "\<not>(matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) (unwrap_decision d) p)"
  shows "filter_approx ((PfRule r)#rs) \<gamma> p d = filter_approx rs \<gamma> p d"
proof(cases d)
  case (Final x1)
  then show ?thesis by simp
next
  case (Preliminary x2)
  then show ?thesis using assms by simp
qed

(*
text\<open>Applying a rule once or several times makes no difference.\<close>
lemma pf_approx_prepend_replicate: 
  "n > 0 \<Longrightarrow> filter_approx (r#rs) \<gamma> p d = filter_approx ((replicate n r)@rs) \<gamma> p d"
proof(induction n arbitrary:d)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof(cases r)
    case (PfRule r)
    then show ?thesis
    proof(cases "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) p")
      case True
      then show ?thesis sorry
    next
      case False
      then have "filter_approx ((PfRule r) # rs) \<gamma> p d = filter_approx ((PfRule r) # ((PfRule r) # rs)) \<gamma> p d" by (rule meh[symmetric])
      then show ?thesis unfolding PfRule using Suc apply simp sorry
    qed
  next
    case (Anchor r b)
    then show ?thesis sorry
  qed
qed


lemma fixedaction_swap:
"pf_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) (m1@m2)) \<gamma> p =
pf_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) (m2@m1)) \<gamma> p"
proof(-)
  have "pf_approx ((map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) m1)@(map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) m2)) \<gamma> p =
pf_approx ((map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) m2)@(map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) m1)) \<gamma> p"
  proof(induction m1)
    case Nil
    then show ?case by simp
  next
    case (Cons m m1)
    then show ?case
    proof(cases "matches \<gamma> m a p")
      case True
      then show ?thesis
      proof(induction m2)
        case Nil
        then show ?case by simp
      next
        case (Cons a m2)
        then show ?case sorry
      qed
    next
      case False
      then show ?thesis sorry
    qed
  qed
  then show ?thesis by simp
qed

corollary fixedaction_reorder: "pf_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) (m1 @ m2 @ m3)) \<gamma> p =
 pf_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) (m2 @ m1 @ m3)) \<gamma> p"
  sorry


text\<open>If the actions are equal, the @{term set} (position and replication independent) of the match expressions can be considered.\<close>
lemma pf_approx_fixaction_matchseteq: "set m1 = set m2 \<Longrightarrow>
        pf_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) m1) \<gamma> p = 
       pf_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) m2) \<gamma> p"
  sorry
*)

subsection\<open>@{term match_list}\<close>
  text\<open>Reducing the firewall semantics to short-circuit matching evaluation\<close>

  fun match_list :: "('a, 'packet) match_tac \<Rightarrow> 'a match_expr list \<Rightarrow> action \<Rightarrow> decision \<Rightarrow> 'packet \<Rightarrow> bool" where
   "match_list \<gamma> [] a d p = False" |
   "match_list \<gamma> (m#ms) a d p = (if matches \<gamma> m a d p then True else match_list \<gamma> ms a d p)"


  lemma match_list_matches: "match_list \<gamma> ms a d p \<longleftrightarrow> (\<exists>m \<in> set ms. matches \<gamma> m a d p)"
    by(induction ms, simp_all)


lemma match_list_False: "\<not>match_list \<gamma> ms a (unwrap_decision d) p \<Longrightarrow> filter_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) ms) \<gamma> p d =
 d"
proof(induction ms)
  case Nil
  then show ?case by (cases d;simp)
next
  case (Cons a ms)
  then show ?case by (cases d;auto)
qed

lemma match_list_True: "match_list \<gamma> ms a d p \<Longrightarrow> filter_approx (map (\<lambda>m. PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>) ms) \<gamma> p (Preliminary d) =
 (case a of Pass \<Rightarrow> (Preliminary decision.Accept) | Block \<Rightarrow> (Preliminary decision.Reject) | action.Match \<Rightarrow> (Preliminary d))"
proof(induction ms arbitrary:d)
case Nil
  then show ?case by simp
next
  case *:(Cons m ms)
  then show ?case
  proof(cases "matches \<gamma> m a d p")
    case True
    then show ?thesis
    proof(cases "match_list \<gamma> ms a (action_to_decision a d) p")
      case True
      then show ?thesis using * apply(cases a) by auto
    next
      case False
      then show ?thesis using * match_list_False[of \<gamma> ms a "(Preliminary (action_to_decision a d))" p] apply(cases a) by auto
    qed
  next
    case False
    then show ?thesis using * by simp
  qed
qed


  text\<open>The key idea behind @{const match_list}: Reducing semantics to match list\<close>
lemma match_list_semantics:
  assumes match_list:"match_list \<gamma> ms1 a (unwrap_decision d) p \<longleftrightarrow> match_list \<gamma> ms2 a (unwrap_decision d) p"
    shows "filter_approx (map (\<lambda>m. (PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>)) ms1) \<gamma> p d = filter_approx (map (\<lambda>m. (PfRule \<lparr>get_action = a, get_quick = False, pf_rule.get_match = m\<rparr>)) ms2) \<gamma> p d"
proof(cases "match_list \<gamma> ms1 a (unwrap_decision d) p")
    case m1T:True
    then have m2T:"match_list \<gamma> ms2 a (unwrap_decision d) p" using match_list by auto
    show ?thesis using m1T m2T by (cases a;cases d;auto simp add: match_list_True unwrap_decision_cases)
  next
    case m1F:False
    then have m2F:"\<not>match_list \<gamma> ms2 a (unwrap_decision d) p" using match_list by auto
    show ?thesis using m1F m2F by (cases a;cases d;auto simp add: match_list_False unwrap_decision_cases)
  qed


  text\<open>We can exploit de-morgan to get a disjunction in the match expression!\<close>
  (*but we need to normalize afterwards, which is quite slow*)
  fun match_list_to_match_expr :: "'a match_expr list \<Rightarrow> 'a match_expr" where
    "match_list_to_match_expr [] = MatchNot MatchAny" |
    "match_list_to_match_expr (m#ms) = MatchOr m (match_list_to_match_expr ms)"
  text\<open>@{const match_list_to_match_expr} constructs a unwieldy @{typ "'a match_expr"} from a list.
        The semantics of the resulting match expression is the disjunction of the elements of the list.
        This is handy because the normal match expressions do not directly support disjunction.
        Use this function with care because the resulting match expression is very ugly!\<close>
  lemma match_list_to_match_expr_disjunction: "match_list \<gamma> ms a d p \<longleftrightarrow> matches \<gamma> (match_list_to_match_expr ms) a d p"
    apply(induction ms rule: match_list_to_match_expr.induct)
     apply(simp add: bunch_of_lemmata_about_matches; fail)
    apply(simp add: MatchOr)
  done

  lemma match_list_singleton: "match_list \<gamma> [m] a d p \<longleftrightarrow> matches \<gamma> m a d p" by(simp)

  lemma match_list_append: "match_list \<gamma> (m1@m2) a d p \<longleftrightarrow> (\<not> match_list \<gamma> m1 a d p \<longrightarrow> match_list \<gamma> m2 a d p)"
      by(induction m1) simp+

  lemma match_list_helper1: "\<not> matches \<gamma> m2 a d p \<Longrightarrow> match_list \<gamma> (map (\<lambda>x. MatchAnd x m2) m1') a d p \<Longrightarrow> False"
    apply(induction m1')
     apply(simp; fail)
    apply(simp split:if_split_asm)
    by(auto dest: matches_dest)
  lemma match_list_helper2: " \<not> matches \<gamma> m a d p \<Longrightarrow> \<not> match_list \<gamma> (map (MatchAnd m) m2') a d p"
    apply(induction m2')
     apply(simp; fail)
    apply(simp split:if_split_asm)
    by(auto dest: matches_dest)
  lemma match_list_helper3: "matches \<gamma> m a d p \<Longrightarrow> match_list \<gamma> m2' a d p \<Longrightarrow> match_list \<gamma> (map (MatchAnd m) m2') a d p"
    apply(induction m2')
     apply(simp; fail)
    apply(simp split:if_split_asm)
    by (simp add: matches_simps)
  lemma match_list_helper4: "\<not> match_list \<gamma> m2' a d p \<Longrightarrow> \<not> match_list \<gamma> (map (MatchAnd aa) m2') a d p "
    apply(induction m2')
     apply(simp; fail)
    apply(simp split:if_split_asm)
    by(auto dest: matches_dest)
  lemma match_list_helper5: " \<not> match_list \<gamma> m2' a d p \<Longrightarrow> \<not> match_list \<gamma> (concat (map (\<lambda>x. map (MatchAnd x) m2') m1')) a d p "
    apply(induction m2')
     apply(simp add:empty_concat; fail)
    apply(simp split:if_split_asm)
    apply(induction m1')
     apply(simp; fail)
    apply(simp add: match_list_append)
    by(auto dest: matches_dest)
  lemma match_list_helper6: "\<not> match_list \<gamma> m1' a d p \<Longrightarrow> \<not> match_list \<gamma> (concat (map (\<lambda>x. map (MatchAnd x) m2') m1')) a d p "
    apply(induction m2')
     apply(simp add:empty_concat; fail)
    apply(simp split:if_split_asm)
    apply(induction m1')
     apply(simp; fail)
    apply(simp add: match_list_append split: if_split_asm)
    by(auto dest: matches_dest)
  
  lemmas match_list_helper = match_list_helper1 match_list_helper2 match_list_helper3 match_list_helper4 match_list_helper5 match_list_helper6
  hide_fact match_list_helper1 match_list_helper2 match_list_helper3 match_list_helper4 match_list_helper5 match_list_helper6

  lemma match_list_map_And1: "matches \<gamma> m1 a d p = match_list \<gamma> m1' a d p \<Longrightarrow>
           matches \<gamma> (MatchAnd m1 m2) a d p \<longleftrightarrow> match_list \<gamma>  (map (\<lambda>x. MatchAnd x m2) m1') a d p"
    apply(induction m1')
     apply(auto dest: matches_dest; fail)[1]
    apply(simp split: if_split_asm)
     apply safe
        apply(simp_all add: matches_simps)
      apply(auto dest: match_list_helper(1))[1]
     by(auto dest: matches_dest)

  lemma matches_list_And_concat: "matches \<gamma> m1 a d p = match_list \<gamma> m1' a d p \<Longrightarrow> matches \<gamma> m2 a d p = match_list \<gamma> m2' a d p \<Longrightarrow>
           matches \<gamma> (MatchAnd m1 m2) a d p \<longleftrightarrow> match_list \<gamma> [MatchAnd x y. x <- m1', y <- m2'] a d p"
    apply(induction m1')
     apply(auto dest: matches_dest; fail)[1]
    apply(simp split: if_split_asm)
     prefer 2
     apply(simp add: match_list_append)
     apply(subgoal_tac "\<not> match_list \<gamma> (map (MatchAnd aa) m2') a d p")
      apply(simp; fail)
     apply safe
               apply(simp_all add: matches_simps match_list_append match_list_helper)
    done

  lemma match_list_concat: "match_list \<gamma> (concat lss) a d p \<longleftrightarrow> (\<exists>ls \<in> set lss. match_list \<gamma> ls a d p)"
    apply(induction lss)
     apply(simp; fail)
    by(auto simp add: match_list_append)
    

end
