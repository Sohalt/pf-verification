theory PF
  imports Iptables_Semantics.L4_Protocol_Flags
          Simple_Firewall.L4_Protocol
          Simple_Firewall.Simple_Packet
          IP_Addresses.IPv4
          PrimitiveMatchers
          Matching
          "HOL-Library.Simps_Case_Conv"
begin

(* Block return semantically equal to Block (without return)*)
datatype action = Pass | Match | Block


record pf_rule =
  r_Action :: action
  r_Quick :: bool
  r_Direction :: "direction option"
  r_On :: "iface option"
  r_Af :: "afspec option"
  r_Proto :: "primitive_protocol list option"
  r_Hosts :: "hosts option"
  r_FilterOpts :: "filteropt list option"

record 'a pf_rule2 =
  get_action :: action
  get_quick :: bool
  get_match :: "'a match_expr"

record anchor_rule =
  Direction :: "direction option"
  On :: "iface option"
  Af :: "afspec option"
  Proto :: "protocol list option"
  Hosts :: "hosts option"
  r_FilterOpts :: "filteropt list option"

record 'a anchor_rule2 =
  get_match :: "'a match_expr"

datatype 'a line =
  Option
  | PfRule "'a pf_rule2"
  | is_Anchor: Anchor "'a anchor_rule2" "'a line list"

quickcheck_generator line constructors: Option, PfRule

type_synonym 'a ruleset = "'a line list"

datatype decision =
  Accept
  | Reject
  | Undecided

fun action_to_decision :: "action \<Rightarrow> decision \<Rightarrow> decision" where
"action_to_decision Pass _ = Accept"|
"action_to_decision Block _ = Reject"|
"action_to_decision action.Match d = d"

case_of_simps action_to_decision_cases: action_to_decision.simps

datatype decision_wrap =
  Final decision
  | Preliminary decision

fun filter_spec :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter_spec [] m p d = d"
|"filter_spec (Option#ls) m p d = filter_spec ls m p d"
|"filter_spec ((PfRule r)#ls) m p d =
(if (matches m (pf_rule2.get_match r) p)
then
(if (pf_rule2.get_quick r)
then (action_to_decision (pf_rule2.get_action r) d)
else (filter_spec ls m p (action_to_decision (pf_rule2.get_action r) d)))
else
filter_spec ls m p d)"
|"filter_spec ((Anchor r b)#ls) m p d =
(if (matches m (anchor_rule2.get_match r) p)
then
(filter_spec (b@ls) m p d)
else
filter_spec ls m p d)"

fun filter :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter _ _ _ (Final d) = Final d"
| "filter [] _ _ d = d"
| "filter (l#ls) m p (Preliminary d) = filter ls m p (case l of
Option \<Rightarrow> (Preliminary d)
| (PfRule r) \<Rightarrow> (if (matches m (pf_rule2.get_match r) p)
then
  (if (get_quick r)
    then (Final (action_to_decision (get_action r) d))
    else (Preliminary (action_to_decision (get_action r) d)))
else (Preliminary d))
| (Anchor r body) \<Rightarrow> (if (matches m (anchor_rule2.get_match r) p)
then filter (body) m p (Preliminary d)
else (Preliminary d))
)"

case_of_simps filter_cases: filter.simps


fun unwrap_decision :: "decision_wrap \<Rightarrow> decision" where
"unwrap_decision (Final d) = d"
|"unwrap_decision (Preliminary d) = d"

case_of_simps unwrap_decision_cases: unwrap_decision.simps



lemma filter_chain:
  shows "filter (l1@l2) m p d = filter l2 m p (filter l1 m p d)"
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
      case Option
then show ?thesis using Prem IH by simp
next
case (PfRule r)
  then show ?thesis
    proof(cases "matches m (pf_rule2.get_match r) p")
    case True
    then show ?thesis unfolding PfRule using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
next
  case (Anchor r l)
  then show ?thesis
  proof(cases "matches m (anchor_rule2.get_match r) p")
    case True
    then show ?thesis using Prem IH by auto
  next
    case False
    then show ?thesis using Prem IH by auto
  qed
qed
qed
qed

definition pf :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision" where
"pf rules m packet = unwrap_decision (filter rules m packet (Preliminary Undecided))"

definition filter' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision_wrap \<Rightarrow> decision_wrap" where
"filter' rules m d = filter rules (\<lambda>a p. m a) () d"

lemma matches_equiv[simp]: "matches (\<lambda>a p. m a packet) me () = matches m me packet"
  by (induction me, auto)

lemma filter_filter'_eq[simp]: "filter' rules (\<lambda>a. m a packet) d = filter rules m packet d"
unfolding filter'_def
by (induction rules m packet d rule: filter.induct) (auto split: line.splits)

definition pf' :: "'a ruleset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> decision" where
"pf' rules m = unwrap_decision (filter' rules m (Preliminary Undecided))"

lemma "pf rules m packet = pf' rules (\<lambda>a. m a packet)"
  unfolding pf_def pf'_def
  by simp



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

(*

ignore options

include (similar to call, includes other file \<rightarrow> inlining)

define tables:
datatype table_rule


regular rules:
datatype pf_rule

anchors:
datatype anchor_rule = Anchor

*)
end