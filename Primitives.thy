theory Primitives
  imports IP_Addresses.IPv4
    IP_Addresses.IPv6
IP_Addresses.Prefix_Match
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

datatype address =
  InterfaceName string
  | InterfaceGroup string
  | Hostname string
  | Ipv4 "32 prefix_match"
  | Ipv6 ipv6addr "128 prefix_match"

datatype table_address =
  isIPv4: IPv4 (ip4:"32 prefix_match")
  | isIPv6: IPv6 (ip6:"128 prefix_match")

datatype table_entry =
TableEntry (ta: table_address)
| is_Negated: TableEntryNegated (ta: table_address)

type_synonym table = "table_entry list"

datatype host =
  Address address
  | NotAddress address
  | Table string
  (* TODO cidr *)

datatype hostspec =
  AnyHost
  | NoRoute
  | UrpfFailed
  | Self
  | Host "host list"
  | Route string

datatype hosts =
AllHosts
| FromTo hostspec "opspec list option" hostspec "opspec list option"
end