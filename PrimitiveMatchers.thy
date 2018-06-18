theory PrimitiveMatchers
  imports Primitives 
          Simple_Firewall.Simple_Packet
          Matching
begin
fun match_interface :: "direction option \<Rightarrow> iface option \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_interface (Some In) (Some iface) p = ((p_iiface p) = iface)" |
"match_interface (Some In) None p = ((p_iiface p) \<noteq> [])" |
"match_interface (Some Out) (Some iface) p = ((p_oiface p) = iface)" |
"match_interface (Some Out) None p = ((p_oiface p) \<noteq> [])" |
"match_interface None (Some iface) p = ((p_iiface p = iface) \<or> (p_oiface p = iface))" |
"match_interface None None p = True"

fun match_iiface :: "iface \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_iiface iface p \<longleftrightarrow> (p_iiface p) = iface"

fun match_oiface :: "iface \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_oiface iface p \<longleftrightarrow> (p_oiface p) = iface"

fun match_af:: "afspec \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_af Inet _ = True" |
"match_af Inet6 _ = False" (* TODO ipv6 *)

(* uses protocol from Simple_Firewall.L4_Protocol, pf doesn't have "ProtoAny" (no protocol specified means "ProtoAny") *)
fun match_proto:: "primitive_protocol list \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_proto [] _ = False"|
"match_proto (p#ps) pkt = ((p_proto pkt = p) \<or> match_proto ps pkt)"

fun match_address :: "address \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_address _ _ = True" -- TODO

fun match_table :: "string \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_table name ip = True" (* TODO *)

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

fun lookup_port :: "identifier \<Rightarrow> 16 word" where
"lookup_port (Name n) = 0" | -- TODO
"lookup_port (Number n) = of_nat n"

(* fun match_unary_op :: "(identifier \<Rightarrow> 'a) \<Rightarrow> unary_op \<Rightarrow> 'a \<Rightarrow> bool" where *)
fun match_unary_op :: "(identifier \<Rightarrow> 16 word) \<Rightarrow> unary_op \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_unary_op lookup (Eq i) x = (x = lookup i)" |
"match_unary_op lookup (NEq i) x = (x \<noteq> lookup i)" |
"match_unary_op lookup (Lt i) x = (x < lookup i)" |
"match_unary_op lookup (LtEq i) x = (x \<le> lookup i)" |
"match_unary_op lookup (Gt i) x = (x > lookup i)" |
"match_unary_op lookup (GtEq i) x = (x \<ge> lookup i)"

(* fun match_binary_op :: "(identifier \<Rightarrow> 'a) \<Rightarrow> binary_op \<Rightarrow> 'a \<Rightarrow> bool" where *)
fun match_binary_op :: "binary_op \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_binary_op (RangeIncl l u) x = (of_nat l \<le> x \<and> x \<le> of_nat u)"|
"match_binary_op (RangeExcl l u) x = (of_nat l < x \<and> x < of_nat u)"|
"match_binary_op (RangeComp l u) x = ((l \<le> u) \<and> \<not>(of_nat l \<le> x \<and> x \<le> of_nat u))"

(* fun match_op :: "(identifier \<Rightarrow> 'i) \<Rightarrow> opspec \<Rightarrow> 'i \<Rightarrow> bool" where *)
fun match_op :: "(identifier \<Rightarrow> 16 word) \<Rightarrow> opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_op lookup (Unary operator) x = match_unary_op lookup operator x" |
"match_op lookup (Binary operator) x = match_binary_op operator x"

fun match_op_port :: "opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_op_port opspec p = match_op lookup_port opspec p"

fun match_port_ops :: "opspec list \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port_ops [] _ = False" |
"match_port_ops (operator#ops) p = (match_op_port operator p \<or> match_port_ops ops p)"

fun match_port :: "opspec list option \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port None _ = True"|
"match_port (Some ops) port = match_port_ops ops port"

fun match_hosts :: "hosts \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_hosts AllHosts _ = True" |
"match_hosts (FromTo from sports to dports) p = (match_hostspec from (p_src p) \<and> match_port sports (p_sport p) \<and> match_hostspec to (p_dst p) \<and> match_port dports (p_dport p))"

fun match_filteropts :: "filteropt list \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_filteropts _ _ = True"

datatype 'i::len common_primitive =
IIface "iface"
| OIface "iface"
| Af "afspec"
| Proto "primitive_protocol list"
| Hosts "hosts"

fun matcher :: "'i::len common_primitive \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"matcher (IIface iface) p = match_iiface iface p"|
"matcher (OIface iface) p = match_oiface iface p"|
"matcher (Af af) p = match_af af p"|
"matcher (Proto proto) p = match_proto proto p"|
"matcher (Hosts hosts) p = match_hosts hosts p"

end