theory Primitives
  imports IP_Addresses.IPv4
 Iptables_Semantics.L4_Protocol_Flags
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
  | Flags ipt_tcp_flags (* taken from iptables_semantics *)

(*
  | IcmpType icmp_type
  | Icmp6Type icmp6_type
  | Tos string
*)

datatype direction = In | Out

type_synonym iface =
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
  AnyHost
  | NoRoute
  | UrpfFailed
  | Self
  | Host "host list"
  | Route string
end