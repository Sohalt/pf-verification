theory pfprefix_PF
  imports 
          "HOL-Library.Simps_Case_Conv"
          pfprefix_Firewall_Common
begin

text\<open>A matcher (parameterized by the type of primitive @{typ 'a} and packet @{typ 'p})
     is a function which just tells whether a given primitive and packet matches.\<close>
type_synonym ('a, 'p) matcher = "'a \<Rightarrow> 'p \<Rightarrow> bool"


text\<open>Given an @{typ "('a, 'p) matcher"} and a match expression, does a packet of type @{typ 'p}
     match the match expression?\<close>
fun matches :: "('a, 'p) matcher \<Rightarrow> 'a match_expr \<Rightarrow> 'p \<Rightarrow> bool" where
"matches \<gamma> (MatchAnd e1 e2) p \<longleftrightarrow> matches \<gamma> e1 p \<and> matches \<gamma> e2 p" |
"matches \<gamma> (MatchNot me) p \<longleftrightarrow> \<not> matches \<gamma> me p" |
"matches \<gamma> (Match e) p \<longleftrightarrow> \<gamma> e p" |
"matches _ MatchAny _ \<longleftrightarrow> True"

lemma "matches \<gamma> (MatchOr e1 e2) p \<longleftrightarrow> matches \<gamma> e1 p \<or> matches \<gamma> e2 p" unfolding MatchOr_def by auto

fun filter_spec :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter_spec [] \<gamma> p d = d" |
"filter_spec ((PfRule r)#ls) \<gamma> p d = (if (matches \<gamma> (pf_rule.get_match r) p)
                                       then (if (pf_rule.get_quick r)
                                              then (action_to_decision (pf_rule.get_action r) d)
                                              else (filter_spec ls \<gamma> p (action_to_decision (pf_rule.get_action r) d)))
                                       else filter_spec ls \<gamma> p d)" |
"filter_spec ((Anchor r b)#ls) \<gamma> p d = (if (matches \<gamma> (anchor_rule.get_match r) p)
                                         then (filter_spec (b@ls) \<gamma> p d)
                                         else filter_spec ls \<gamma> p d)"

fun filter :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter _ _ _ (Final d) = Final d" |
"filter [] _ _ d = d" |
"filter (l#ls) \<gamma> p (Preliminary d) =
  filter ls \<gamma> p (case l of
                  (PfRule r) \<Rightarrow> (if (matches \<gamma> (pf_rule.get_match r) p)
                                               then (if (get_quick r)
                                                      then (Final (action_to_decision (get_action r) d))
                                                      else (Preliminary (action_to_decision (get_action r) d)))
                                               else (Preliminary d))
                  | (Anchor r body) \<Rightarrow> (if (matches \<gamma> (anchor_rule.get_match r) p)
                                                    then filter (body) \<gamma> p (Preliminary d)
                                                    else (Preliminary d)))"

case_of_simps filter_cases: filter.simps


lemma filter_chain:
  shows "filter (l1@l2) \<gamma> p d = filter l2 \<gamma> p (filter l1 \<gamma> p d)"
proof(induction l1 arbitrary: d)
  case Nil
  then show ?case
  proof(cases d)
    case (Final x1)
    then show ?thesis by simp
  next
    case (Preliminary x2)
    then show ?thesis by simp
  qed
next
  case IH:(Cons a l1)
  then show ?case
  proof(cases d)
    case (Final x1)
    then show ?thesis by simp
  next
    case Prem: (Preliminary x2)
    then show ?thesis
    proof(cases a)
case (PfRule r)
  then show ?thesis
    proof(cases "matches \<gamma> (pf_rule.get_match r) p")
    case True
    then show ?thesis unfolding PfRule using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
next
  case (Anchor r l)
  then show ?thesis
  proof(cases "matches \<gamma> (anchor_rule.get_match r) p")
    case True
    then show ?thesis using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
qed
qed
qed

lemma "filter_spec rules \<gamma> p start_decision = unwrap_decision (filter rules \<gamma> p (Preliminary start_decision))"
proof(induction rules \<gamma> p start_decision rule: filter_spec.induct)
  case (1 \<gamma> p d)
  then show ?case by simp
next
  case (2 ls \<gamma> p d)
  then show ?case by simp
next
  case IH: (3 r b ls \<gamma> p d)
  then show ?case
  proof(cases "matches \<gamma> (anchor_rule.get_match r) p")
    case True
    then show ?thesis using IH by (auto simp: filter_chain)
  next
    case False
    then show ?thesis using IH by auto
  qed
qed

(* default behavior is Accept *)
definition pf :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision" where
"pf rules \<gamma> packet = unwrap_decision (filter rules \<gamma> packet (Preliminary Accept))"

definition filter' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter' rules \<gamma> d = filter rules (\<lambda>a p. \<gamma> a) () d"

lemma matches_equiv[simp]: "matches (\<lambda>a p. \<gamma> a packet) me () = matches \<gamma> me packet"
  by (induction me, auto)

lemma filter_filter'_eq[simp]: "filter' rules (\<lambda>a. \<gamma> a packet) d = filter rules \<gamma> packet d"
unfolding filter'_def
by (induction rules \<gamma> packet d rule: filter.induct) (auto split: line.splits)

(* default behavior is Accept *)
definition pf' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision" where
"pf' rules \<gamma> = unwrap_decision (filter' rules \<gamma> (Preliminary Accept))"

lemma "pf rules \<gamma> packet = pf' rules (\<lambda>a. \<gamma> a packet)"
  unfolding pf_def pf'_def
  by simp

lemma filter_to_pf:
  assumes "\<forall> d. (filter l1 m p d = filter l2 m p d)"
  shows "pf l1 m p = pf l2 m p" unfolding pf_def using assms by simp

(*
definition test_packet :: "('i::len) simple_packet" where
"test_packet \<equiv>
\<lparr>
          p_iiface = ''eth1'', p_oiface = '''',
          p_src = 0, p_dst = 0,
          p_proto = TCP, p_sport = 0, p_dport = 0,
          p_tcp_flags = {TCP_SYN},
          p_payload = ''arbitrary payload''
          \<rparr>"

lemma "pf [] matcher test_packet = Undecided" by code_simp

lemma "pf [
PfRule \<lparr>
  get_action = Pass,
  get_quick = False,
  get_match = MatchAny
\<rparr>
] matcher test_packet = Accept" by code_simp

lemma "pf [
PfRule \<lparr>
  get_action = Block,
  get_quick = False,
  get_match = MatchAny
\<rparr>
] matcher test_packet = Reject" by code_simp

lemma "pf [
PfRule \<lparr>
  get_action = Match,
  get_quick = False,
  get_match = MatchAny
\<rparr>
] matcher test_packet = Undecided" by code_simp

lemma "pf [
PfRule \<lparr>
  get_action = Pass,
  get_quick = True,
  get_match = MatchAny
\<rparr>,
PfRule \<lparr>
  get_action = Block,
  get_quick = True,
  get_match = MatchAny
\<rparr>
] matcher test_packet = Accept" by code_simp

lemma "pf [
PfRule \<lparr>
  get_action = Block,
  get_quick = True,
  get_match = MatchAny
\<rparr>,
PfRule \<lparr>
  get_action = Pass,
  get_quick = True,
  get_match = MatchAny
\<rparr>
] matcher test_packet = Reject" by code_simp
*)

end