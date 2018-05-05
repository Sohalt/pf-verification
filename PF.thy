theory PF
  imports Iptables_Semantics.L4_Protocol_Flags
          Simple_Firewall.L4_Protocol
          Simple_Firewall.Simple_Packet
          IP_Addresses.IPv4
          PrimitiveMatchers
begin

(* Block return semantically equal to Block (without return)*)
datatype action = Pass | Match | Block

(* Taken from Iptaples_Semantics/Firewall_Common.thy*)
datatype 'a match_expr = Match 'a
                       | MatchNot "'a match_expr"
                       | MatchAnd "'a match_expr" "'a match_expr"
                       | MatchAny

definition MatchOr :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" where
  "MatchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2))"
(* end *)

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

fun match_pfrule :: "pf_rule \<Rightarrow> (32 simple_packet) \<Rightarrow> bool" where
"match_pfrule r p = 
((match_interface (r_Direction r) (r_On r) p)
\<and> (case (r_Af r) of Some(af) \<Rightarrow> (match_af af p) | None \<Rightarrow> True)
\<and> (case (r_Proto r) of Some(proto) \<Rightarrow> (match_proto proto p) | None \<Rightarrow> True)
\<and> (case (r_Hosts r) of Some(hosts) \<Rightarrow> (match_hosts hosts p) | None \<Rightarrow> True)
\<and> (case (r_FilterOpts r) of (Some fo) \<Rightarrow> (match_filteropts fo p) | None \<Rightarrow> True))"

fun match_anchorrule :: "anchor_rule \<Rightarrow> (32 simple_packet) \<Rightarrow> bool" where
"match_anchorrule _ _ = True" (* TODO *)

fun action_to_decision :: "action \<Rightarrow> decision \<Rightarrow> decision" where
"action_to_decision Pass _ = Accept"|
"action_to_decision Block _ = Reject"|
"action_to_decision action.Match d = d"

fun filter :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision \<Rightarrow> decision" where
"filter [] _ _ d = d"
| "filter (Option # rs) m p d = filter rs m p d"
| "filter ((PfRule r) # rs) m p d = (if (matches m (pf_rule2.get_match r) p)
then
(if (get_quick r) then (action_to_decision (get_action r) d)
else filter rs m p (action_to_decision (get_action r) d))
else filter rs m p d)"
| "filter ((Anchor r l) # rs) m p d = (if (matches m (anchor_rule2.get_match r) p)
then filter (l @ rs) m p d
else filter rs m p d)"

fun pf :: "'a ruleset \<Rightarrow> ('a, 'p) matcher \<Rightarrow> 'p \<Rightarrow> decision" where
"pf rules matcher packet = filter rules matcher packet Undecided"

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