theory PrimitiveMatchers
  imports Primitives
          Simple_Firewall.Simple_Packet
          Iptables_Semantics.Ternary
          Matching
begin
fun match_interface :: "iface \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_interface iface p = (((p_iiface p) = iface) \<or> ((p_oiface p) = iface))"

fun match_direction :: "direction \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_direction In p \<longleftrightarrow> (p_iiface p) \<noteq> ''''"|
"match_direction Out p \<longleftrightarrow> (p_oiface p) \<noteq> ''''"

fun match_af:: "afspec \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_af Inet p = True" (* (len_of (TYPE ('i)) = 32)" *)
|"match_af Inet6 p = False" (* TODO ipv6 *)

(* uses protocol from Simple_Firewall.L4_Protocol, pf doesn't have "ProtoAny" (no protocol specified means "ProtoAny") *)
fun match_proto:: "primitive_protocol \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_proto proto p \<longleftrightarrow> p_proto p = proto"



(* TODO ipv4 ipv6 versions
fun match_host :: "host \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_host (Address addr) ip = match_address addr ip"|
"match_host (NotAddress addr) ip = (\<not> (match_address addr ip))"|
"match_host (Table t) ip = match_table t ip"

fun match_hostlist :: "host list \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_hostlist [] _ = False" |
"match_hostlist (h#hs) ip = (match_host h ip \<or> match_hostlist hs ip)"

fun match_hostspec:: "hostspec \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_hostspec AnyHost _ = True" |
"match_hostspec NoRoute _ = True" | (* TODO: unknown *)
"match_hostspec UrpfFailed _ = True" | (* TODO: unknown *)
"match_hostspec Self _ = True" | (* TODO: unknown *)
"match_hostspec (Host hostlist) ip = match_hostlist hostlist ip" |
"match_hostspec (Route route) _ = True" (* TODO: unknown *)

*)

(* fun match_unary_op :: "(identifier \<Rightarrow> 'a) \<Rightarrow> unary_op \<Rightarrow> 'a \<Rightarrow> bool" where *)
fun match_unary_op :: "unary_op \<Rightarrow> nat \<Rightarrow> bool" where
"match_unary_op (Eq i) x = (x = i)" |
"match_unary_op (NEq i) x = (x \<noteq> i)" |
"match_unary_op (Lt i) x = (x < i)" |
"match_unary_op (LtEq i) x = (x \<le> i)" |
"match_unary_op (Gt i) x = (x > i)" |
"match_unary_op (GtEq i) x = (x \<ge> i)"

(* fun match_binary_op :: "(identifier \<Rightarrow> 'a) \<Rightarrow> binary_op \<Rightarrow> 'a \<Rightarrow> bool" where *)
fun match_binary_op :: "binary_op \<Rightarrow> nat \<Rightarrow> bool" where
"match_binary_op (RangeIncl l u) x = (l \<le> x \<and> x \<le> u)"|
"match_binary_op (RangeExcl l u) x = (l < x \<and> x < u)"|
"match_binary_op (RangeComp l u) x = ((l \<le> u) \<and> \<not>(l \<le> x \<and> x \<le> u))"

fun match_op :: "opspec \<Rightarrow> nat \<Rightarrow> bool" where
"match_op (Unary operator) x = match_unary_op operator x" |
"match_op (Binary operator) x = match_binary_op operator x"

definition match_port :: "opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port operator port = match_op operator (unat port)"

(* TODO ipv4 ipv6 versions
fun match_hosts :: "hosts \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_hosts AllHosts _ = True" |
"match_hosts (FromTo from sports to dports) p = (match_hostspec from (p_src p) \<and> match_port sports (p_sport p) \<and> match_hostspec to (p_dst p) \<and> match_port dports (p_dport p))"
*)

fun common_matcher :: "common_primitive \<Rightarrow> 32 simple_packet \<Rightarrow> ternaryvalue" where
"common_matcher (Src hosts) p = TernaryUnknown"| (* FIXME *)
"common_matcher (Dst hosts) p = TernaryUnknown"| (* FIXME *)
"common_matcher (Src_OS _) _ = TernaryUnknown"|
"common_matcher (Src_Ports ports) p = bool_to_ternary (match_port ports (p_sport p))"|
"common_matcher (Dst_Ports ports) p = bool_to_ternary (match_port ports (p_dport p))"|
"common_matcher (Direction dir) p = bool_to_ternary (match_direction dir p)"|
"common_matcher (Interface (InterfaceName interface)) p = bool_to_ternary (match_interface interface p)"|
"common_matcher (Interface (InterfaceGroup _)) p = TernaryUnknown"|
"common_matcher (Address_Family af) p = bool_to_ternary (match_af af p)"|
"common_matcher (Protocol proto) p = bool_to_ternary (match_proto proto p)"|
"common_matcher (L4_Flags flags) p = bool_to_ternary (match_tcp_flags flags  (p_tcp_flags p))"|
"common_matcher (Extra _) _ = TernaryUnknown"


end