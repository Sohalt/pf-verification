theory PrimitiveMatchers
  imports Primitives
          Simple_Firewall.Simple_Packet
          Iptables_Semantics.Ternary
          Matching
          Tables
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

fun match_unary_op :: "unary_op \<Rightarrow> nat \<Rightarrow> bool" where
"match_unary_op (Eq i) x = (x = i)" |
"match_unary_op (NEq i) x = (x \<noteq> i)" |
"match_unary_op (Lt i) x = (x < i)" |
"match_unary_op (LtEq i) x = (x \<le> i)" |
"match_unary_op (Gt i) x = (x > i)" |
"match_unary_op (GtEq i) x = (x \<ge> i)"

fun match_binary_op :: "binary_op \<Rightarrow> nat \<Rightarrow> bool" where
"match_binary_op (RangeIncl l u) x = (l \<le> x \<and> x \<le> u)"|
"match_binary_op (RangeExcl l u) x = (l < x \<and> x < u)"|
"match_binary_op (RangeComp l u) x = ((l \<le> u) \<and> \<not>(l \<le> x \<and> x \<le> u))"

fun match_op :: "opspec \<Rightarrow> nat \<Rightarrow> bool" where
"match_op (Unary operator) x = match_unary_op operator x" |
"match_op (Binary operator) x = match_binary_op operator x"

definition match_port :: "opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port operator port = match_op operator (unat port)"

record pfcontext = 
  get_tables :: "string \<rightharpoonup> table"
(*  get_routes :: "routes option" *)

definition lookup_table :: "pfcontext \<Rightarrow> string \<Rightarrow> table" where
"lookup_table ctx name = (case (get_tables ctx) name of (Some t) \<Rightarrow> t | None \<Rightarrow> [])"

(* TODO ipv6 *)
fun match_hosts :: "pfcontext \<Rightarrow> hostspec \<Rightarrow> 32 word \<Rightarrow> ternaryvalue" where
"match_hosts _ AnyHost _ = bool_to_ternary True" |
"match_hosts _ (Address addr) p_addr =
(case addr of
 (IPv4 a) \<Rightarrow> bool_to_ternary (prefix_match_semantics a p_addr)
| (IPv6 _) \<Rightarrow> TernaryUnknown)"|
"match_hosts ctx NoRoute _ = TernaryUnknown" |
"match_hosts ctx (Route _) _ = TernaryUnknown" |
"match_hosts ctx (Table name) p_addr = bool_to_ternary (match_table_v4 (lookup_table ctx name) p_addr)"


fun match_hosts_src :: "pfcontext \<Rightarrow> hostspec_from \<Rightarrow> 32 word \<Rightarrow> ternaryvalue" where
"match_hosts_src ctx (Hostspec h) a = match_hosts ctx h a" |
"match_hosts_src ctx UrpfFailed a = TernaryUnknown"

fun common_matcher :: "pfcontext \<Rightarrow> common_primitive \<Rightarrow> 32 simple_packet \<Rightarrow> ternaryvalue" where
"common_matcher ctx (Src hosts) p = match_hosts_src ctx hosts (p_src p)"|
"common_matcher ctx (Dst hosts) p = match_hosts ctx hosts (p_dst p)"|
"common_matcher _ (Src_OS _) _ = TernaryUnknown"|
"common_matcher _ (Src_Ports ports) p = bool_to_ternary (match_port ports (p_sport p))"|
"common_matcher _ (Dst_Ports ports) p = bool_to_ternary (match_port ports (p_dport p))"|
"common_matcher _ (Direction dir) p = bool_to_ternary (match_direction dir p)"|
"common_matcher _ (Interface (InterfaceName interface)) p = bool_to_ternary (match_interface interface p)"|
"common_matcher ctx (Interface (InterfaceGroup _)) p = TernaryUnknown"|
"common_matcher _ (Address_Family af) p = bool_to_ternary (match_af af p)"|
"common_matcher _ (Protocol proto) p = bool_to_ternary (match_proto proto p)"|
"common_matcher _ (L4_Flags flags) p = bool_to_ternary (match_tcp_flags flags  (p_tcp_flags p))"|
"common_matcher _ (Extra _) _ = TernaryUnknown"


end