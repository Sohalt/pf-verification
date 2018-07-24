theory PrimitiveMatchers
  imports Primitives
          Simple_Firewall.Simple_Packet
          Iptables_Semantics.Ternary
          Tables
          Firewall_Common
begin
fun match_interface :: "string \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_interface iface p = (((p_iiface p) = iface) \<or> ((p_oiface p) = iface))"

fun match_direction :: "direction \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_direction In p \<longleftrightarrow> (p_iiface p) \<noteq> ''''"|
"match_direction Out p \<longleftrightarrow> (p_oiface p) \<noteq> ''''"

fun match_af:: "afspec \<Rightarrow> 'i::len0 simple_packet \<Rightarrow> bool" where
"match_af Inet p \<longleftrightarrow> len_of TYPE ('i) = 32"
|"match_af Inet6 p \<longleftrightarrow> len_of TYPE ('i) = 128"

(* uses protocol from Simple_Firewall.L4_Protocol, pf doesn't have "ProtoAny" (no protocol specified means "ProtoAny") *)
fun match_proto:: "primitive_protocol \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_proto proto p \<longleftrightarrow> p_proto p = proto"

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
"match_binary_op (RangeComp l u) x = ((l \<le> u) \<and> \<not>(l \<le> x \<and> x \<le> u))"

fun match_op :: "'i::ord opspec \<Rightarrow> 'i \<Rightarrow> bool" where
"match_op (Unary operator) x = match_unary_op operator x" |
"match_op (Binary operator) x = match_binary_op operator x"

definition match_port :: "16 word opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port operator port = match_op operator port"

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

(* normalize matches to representation closest to simple_matcher *)

fun match_or :: "'a list \<Rightarrow> 'a match_expr" where
"match_or [] = MatchNot MatchAny" |
"match_or (x#xs) = MatchOr (Match x) (match_or xs)"

fun partition_ip_set :: "'i::len word set \<Rightarrow> 'i prefix_match list" where
"partition_ip_set _ = []" (* TODO *)

lemma partition_ip_set : "a \<in> addrs \<longleftrightarrow> (\<exists> pfxm \<in> (set (partition_ip_set addrs)). prefix_match_semantics pfxm a)"
  sorry

fun remove_table :: "pfcontext \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"remove_table ctx (Match (Src (Hostspec (Table name)))) = match_or (map (\<lambda>a. (Src (Hostspec (Address (IPv4 a))))) (partition_ip_set (table_to_set_v4 (lookup_table ctx name))))" |
"remove_table ctx (Match (Dst (Table name))) = match_or (map (\<lambda>a. (Dst (Address (IPv4 a)))) (partition_ip_set (table_to_set_v4 (lookup_table ctx name))))" |
"remove_table _ m = m"

fun normalize_ports' :: "_ word opspec \<Rightarrow> _ word opspec list" where
"normalize_ports' (Unary (Eq p)) = [(Binary (RangeIncl p p))]" |
"normalize_ports' (Unary (NEq p)) = [(Binary (RangeIncl 0 (p - 1))), (Binary (RangeIncl (p + 1) max_word))]" |
"normalize_ports' (Unary (GtEq p)) = [(Binary (RangeIncl p max_word))]" |
"normalize_ports' (Unary (Gt p)) = [(Binary (RangeIncl (p + 1) max_word))]" |
"normalize_ports' (Unary (LtEq p)) = [(Binary (RangeIncl 0 p))]" |
"normalize_ports' (Unary (Lt p)) = [(Binary (RangeIncl 0 (p - 1)))]" |
"normalize_ports' (Binary (RangeIncl from to)) = [(Binary (RangeIncl from to))]" |
"normalize_ports' (Binary (RangeExcl from to)) = [(Binary (RangeIncl (from + 1) (to -1)))]" |
"normalize_ports' (Binary (RangeComp from to)) = [(Binary (RangeIncl 0 from)), (Binary (RangeIncl to max_word))]"

fun normalize_ports :: "common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
"normalize_ports (Match (Src_Ports ports)) = match_or (map (\<lambda>p. (Src_Ports p)) (normalize_ports' ports))" |
"normalize_ports (Match (Dst_Ports ports)) = match_or (map (\<lambda>p. (Dst_Ports p)) (normalize_ports' ports))" |
"normalize_ports m = m"

lemma normalize_ports : "matches \<gamma> m p \<longleftrightarrow> matches \<gamma> (normalize_ports m) p"
proof


end