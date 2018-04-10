theory PF
  imports Iptables_Semantics.L4_Protocol_Flags
          Simple_Firewall.L4_Protocol
          Simple_Firewall.Simple_Packet
          IP_Addresses.IPv4
          PrimitiveMatchers
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

record anchor_rule =
  Direction :: "direction option"
  On :: "iface option"
  Af :: "afspec option"
  Proto :: "protocol list option"
  Hosts :: "hosts option"

datatype line = 
  Option
  | PfRule "pf_rule"
  | Anchor anchor_rule "line list"


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

fun filter :: "line list \<Rightarrow> 32 simple_packet \<Rightarrow> decision \<Rightarrow> decision" where
"filter [] _ d = d"
| "filter (Option # rs) p d = filter rs p d"
| "filter ((PfRule rule) # rs) p d = (if (match_pfrule rule p) 
then filter rs p (case (r_Action rule) of Pass \<Rightarrow> Accept | Block \<Rightarrow> Reject | Match \<Rightarrow> d)
else filter rs p d)"
| "filter ((Anchor rule l) # rs) p d = (if (match_anchorrule rule p)
then filter (l @ rs) p d
else filter rs p d)"

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