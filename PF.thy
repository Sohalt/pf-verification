theory PF
  imports Iptables_Semantics.L4_Protocol_Flags
          Simple_Firewall.L4_Protocol
          Simple_Firewall.Simple_Packet
          IP_Addresses.IPv4
begin

datatype identifier =
  Name string
  | Number nat

datatype unary_op =
  Eq identifier
  | NEq identifier
  | Lt identifier
  | LtEq identifier
  | Gt identifier
  | GtEq identifier

datatype binary_op =
  RangeIncl nat nat
  | RangeExcl nat nat
  | RangeComp nat nat

datatype opspec =
  Unary unary_op
  | Binary binary_op


datatype filteropt =
  User "opspec list"
  | Group "opspec list"
  | Flags ipt_tcp_flags
(*
  | IcmpType icmp_type
  | Icmp6Type icmp6_type
  | Tos string
*)


(* Block return semantically equal to Block (without return)*)
datatype action = Pass | Match | Block

datatype direction = In | Out

datatype iface =
  string

datatype afspec =
  Inet
  | Inet6

datatype host =
  Address ipv4addr
  | NotAddress ipv4addr
  | HostName string
  (* TODO cidr *)

datatype hostspec =
  Any
  | NoRoute
  | UrpfFailed
  | Self
  | Host "host list"
  | Route string

(*
record pf_rule = 
  Action :: action 
  Direction :: "direction option"
  Quick :: bool
  On :: "iface option"
  Af :: "afspec option"
  Proto :: "protocol list"
  Hosts :: "hostspec option"
  FilterOpts :: "(filteropt list) option"
*)

record pf_rule =
  r_action :: action
  r_address :: ipv4addr

type_synonym protospec = "protocol list"

record anchor_rule =
  Direction :: "direction option"
  On :: "iface option"
  Af :: "afspec option"
  Proto :: "protospec option"
  Hosts :: "hostspec option"

datatype line = 
  Option
  | PfRule "pf_rule"
  | Anchor anchor_rule "line list"


datatype decision =
  Accept
  | Reject
  | Undecided

fun match_pfrule :: "pf_rule \<Rightarrow> (32 simple_packet) \<Rightarrow> bool" where
"match_pfrule r p \<longleftrightarrow> ((r_address r) = (p_dst p))" (* TODO *)

fun match_anchorrule :: "anchor_rule \<Rightarrow> (32 simple_packet) \<Rightarrow> bool" where
"match_anchorrule _ _ = True" (* TODO *)

fun filter :: "line list \<Rightarrow> 32 simple_packet \<Rightarrow> decision \<Rightarrow> decision" where
"filter [] _ d = d"
| "filter (Option # rs) p d = filter rs p d"
| "filter ((PfRule rule) # rs) p d = (if (match_pfrule rule p) 
then filter rs p (case (r_action rule) of Pass \<Rightarrow> Accept | Block \<Rightarrow> Reject | Match \<Rightarrow> d)
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