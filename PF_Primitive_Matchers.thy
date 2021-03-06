theory PF_Primitive_Matchers
  imports PF_Primitives
          Simple_Firewall.Simple_Packet
          PF_Tables
          PF_Firewall_Common
          "SemanticsTernary/PF_Unknown_Match_Tacs"
begin

fun match_interface :: "pfcontext \<Rightarrow> ifspec option \<Rightarrow> direction option \<Rightarrow> 32 simple_packet \<Rightarrow> ternaryvalue" where
"match_interface ctx (Some (InterfaceGroup _)) _ _ = TernaryUnknown" |
"match_interface _ (Some (InterfaceName iface)) None p = bool_to_ternary (((p_iiface p) = iface) \<or> ((p_oiface p) = iface))" |
"match_interface _ (Some (InterfaceName iface)) (Some In) p = bool_to_ternary ((p_iiface p) = iface)" |
"match_interface _ (Some (InterfaceName iface)) (Some Out) p = bool_to_ternary ((p_oiface p) = iface)" |
"match_interface _ None (Some In) p = bool_to_ternary ((p_iiface p) \<noteq> '''')" |
"match_interface _ None (Some Out) p = bool_to_ternary ((p_oiface p) \<noteq> '''')" |
"match_interface _ None None _ = TernaryFalse"


fun match_af:: "afspec \<Rightarrow> 'i::len0 simple_packet \<Rightarrow> bool" where
"match_af Inet p \<longleftrightarrow> len_of TYPE ('i) = 32"
|"match_af Inet6 p \<longleftrightarrow> len_of TYPE ('i) = 128"


fun match_unary_op :: "'i::ord unary_op \<Rightarrow> 'i \<Rightarrow> bool" where
"match_unary_op (Eq i) x = (x = i)" |
"match_unary_op (NEq i) x = (x \<noteq> i)" |
"match_unary_op (Lt i) x = (x < i)" |
"match_unary_op (LtEq i) x = (x \<le> i)" |
"match_unary_op (Gt i) x = (x > i)" |
"match_unary_op (GtEq i) x = (x \<ge> i)"

fun match_binary_op :: "'i::ord binary_op \<Rightarrow> 'i \<Rightarrow> bool" where
"match_binary_op (RangeIncl l u) x = (l \<le> x \<and> x \<le> u)"|
"match_binary_op (RangeExcl l u) x = (l < x \<and> x < u)"|
"match_binary_op (RangeComp l u) x = (l > x \<or> x > u)"

fun match_op :: "'i::ord opspec \<Rightarrow> 'i \<Rightarrow> bool" where
"match_op (Unary operator) x = match_unary_op operator x" |
"match_op (Binary operator) x = match_binary_op operator x"

definition match_port :: "16 word opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port operator port = match_op operator port"


(* TODO ipv6 version *)
fun match_hosts :: "pfcontext \<Rightarrow> hostspec \<Rightarrow> 32 word \<Rightarrow> ternaryvalue" where
"match_hosts _ AnyHost _ = bool_to_ternary True" |
"match_hosts _ (Address addr) p_addr =
(case addr of
 (IPv4 a) \<Rightarrow> bool_to_ternary (prefix_match_semantics a p_addr)
| (IPv6 _) \<Rightarrow> TernaryFalse)"|
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
"common_matcher _ (Src_Ports (L4Ports proto ports)) p = 
  bool_to_ternary ((proto = (p_proto p)) \<and> match_port ports (p_sport p))"|
"common_matcher _ (Dst_Ports (L4Ports proto ports)) p = 
  bool_to_ternary ((proto = (p_proto p)) \<and> match_port ports (p_dport p))"|
"common_matcher ctx (Interface interface direction) p = 
  match_interface ctx interface direction p"|
"common_matcher _ (Address_Family af) p = bool_to_ternary (match_af af p)"|
"common_matcher _ (Protocol proto) p = bool_to_ternary (match_proto proto (p_proto p))"|
"common_matcher _ (L4_Flags flags) p = bool_to_ternary (match_tcp_flags flags  (p_tcp_flags p))"|
"common_matcher _ (Extra _) _ = TernaryUnknown"

end