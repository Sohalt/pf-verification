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
  | Anchor "'a anchor_rule2" "'a line list"

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

thm action_to_decision.simps
thm action_to_decision_cases

datatype decision_wrap =
  Final decision
  | Preliminary decision

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
(*
fun filter :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter [] _ _ d = d"
| "filter (l#ls) m p d = (case l of
Option \<Rightarrow> filter ls m p d
| (PfRule r) \<Rightarrow> (if (matches m (pf_rule2.get_match r) p)
then
(if (get_quick r) then (action_to_decision (get_action r) d)
else filter ls m p (action_to_decision (get_action r) d))
else filter ls m p d)
| (Anchor r body) \<Rightarrow> (if (matches m (anchor_rule2.get_match r) p)
then filter (body @ ls) m p d
else filter ls m p d)
)"
*)
(*
| "filter (Option # rs) m p d = filter rs m p d"
| "filter ((PfRule r) # rs) m p d = (if (matches m (pf_rule2.get_match r) p)
then
(if (get_quick r) then (action_to_decision (get_action r) d)
else filter rs m p (action_to_decision (get_action r) d))
else filter rs m p d)"
| "filter ((Anchor r l) # rs) m p d = (if (matches m (anchor_rule2.get_match r) p)
then filter (l @ rs) m p d
else filter rs m p d)"*)

fun pf :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision" where
"pf rules m packet = (case (filter rules m packet (Preliminary Undecided)) of
(Final d) \<Rightarrow> d
|(Preliminary d) \<Rightarrow> d)"

definition test_packet :: "32 simple_packet" where
"test_packet \<equiv>
\<lparr>
          p_iiface = ''eth1'', p_oiface = '''',
          p_src = 0, p_dst = 0,
          p_proto = TCP, p_sport = 0, p_dport = 0,
          p_tcp_flags = {TCP_SYN},
          p_payload = ''arbitrary payload''
          \<rparr>"

value "filter [] test_packet Undecided"
value "filter [
PfRule \<lparr>
  r_Action = Pass,
  r_Quick = False,
  r_Direction = Some In,
  r_On = None,
  r_Af = None,
  r_Proto = None,
  r_Hosts = None,
  r_FilterOpts = None
\<rparr>
] test_packet Undecided"
value "filter [
PfRule \<lparr>
  r_Action = Block,
  r_Quick = False,
  r_Direction = Some In,
  r_On = None,
  r_Af = None,
  r_Proto = None,
  r_Hosts = None,
  r_FilterOpts = None
\<rparr>
] test_packet Undecided"
value "filter [
PfRule \<lparr>
  r_Action = Block,
  r_Quick = False,
  r_Direction = Some Out,
  r_On = None,
  r_Af = None,
  r_Proto = None,
  r_Hosts = None,
  r_FilterOpts = None
\<rparr>
] test_packet Undecided"

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