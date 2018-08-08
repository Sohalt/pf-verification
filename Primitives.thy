theory pfprefix_Primitives
imports IP_Addresses.IPv4
        IP_Addresses.IPv6
        IP_Addresses.Prefix_Match
        Iptables_Semantics.L4_Protocol_Flags
begin

(* names for users, groups, ports get resolved to numbers in the pfctl dump *)
datatype 'i unary_op =
  Eq "'i"
  | NEq "'i"
  | Lt "'i"
  | LtEq "'i"
  | Gt "'i"
  | GtEq "'i"

datatype 'i binary_op =
  is_RangeIncl: RangeIncl "'i" "'i"
  | RangeExcl "'i" "'i"
  | RangeComp "'i" "'i"

datatype 'i opspec =
  Unary "'i unary_op"
  | Binary "'i binary_op"

datatype filteropt =
  User "16 word opspec list"
  | Group "32 word opspec list"
  | Flags ipt_tcp_flags (* taken from iptables_semantics *)


(*
  | IcmpType icmp_type
  | Icmp6Type icmp6_type
  | Tos string
*)

datatype direction = In | Out

datatype ifspec =
  InterfaceName string
  | InterfaceGroup string

datatype afspec =
  Inet
  | Inet6

datatype address =
  isIPv4: IPv4 (ip4:"32 prefix_match")
  | isIPv6: IPv6 (ip6:"128 prefix_match")

datatype table_entry =
TableEntry (ta: address)
| is_Negated: TableEntryNegated (ta: address)

type_synonym table = "table_entry list"

datatype hostspec =
  AnyHost
  | NoRoute
  | Address address
  | Route string
  | Table string

datatype hostspec_from =
  Hostspec hostspec
  | UrpfFailed

record pfcontext =
  get_tables :: "string \<rightharpoonup> table"
 (* get_ifgroups :: "string \<rightharpoonup> string list"
    get_routes :: "routes option" *)

datatype common_primitive =
is_Src: Src (src_sel: hostspec_from) |
is_Src_OS: Src_OS (src_os_sel: string) |
is_Dst: Dst (dst_sel: hostspec) |
is_Src_Ports: Src_Ports (src_ports_sel: "16 word opspec") |
is_Dst_Ports: Dst_Ports (dst_ports_sel: "16 word opspec") |
is_Interface: Interface (interface_sel: "ifspec option") (direction_sel: "direction option") |
is_Address_Family: Address_Family (address_family_sel: afspec) |
is_Protocol: Protocol (protocol_sel: primitive_protocol) |
is_L4_Flags: L4_Flags (l4_flags_sel: ipt_tcp_flags) |
is_Extra: Extra (extra_sel: string)

definition valid_table :: "table \<Rightarrow> bool" where
"valid_table table \<longleftrightarrow> (\<forall> t \<in> set table . (case (ta t) of (IPv4 a) \<Rightarrow> valid_prefix a | (IPv6 a) \<Rightarrow> valid_prefix a))"

definition lookup_table :: "pfcontext \<Rightarrow> string \<Rightarrow> table" where
"lookup_table ctx name = (case (get_tables ctx) name of (Some t) \<Rightarrow> t | None \<Rightarrow> [])"

fun good_hostspec :: "pfcontext \<Rightarrow> hostspec \<Rightarrow> bool" where
"good_hostspec _ (Address (IPv4 a)) = valid_prefix a" |
"good_hostspec _ (Address (IPv6 a)) = valid_prefix a" |
"good_hostspec ctx (Table name) = valid_table (lookup_table ctx name)" |
"good_hostspec _ _ = True"

fun good_primitive :: "pfcontext \<Rightarrow> common_primitive \<Rightarrow> bool" where
"good_primitive ctx (Src (Hostspec h)) = good_hostspec ctx h" |
"good_primitive ctx (Dst h) = good_hostspec ctx h" |
"good_primitive _ _ = True"

end