theory PrimitiveMatchers
  imports Primitives 
Simple_Firewall.Simple_Packet
begin
fun match_interface :: "direction option \<Rightarrow> iface option \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_interface (Some In) (Some iface) p = ((p_iiface p) = iface)" |
"match_interface (Some In) None p = ((p_iiface p) \<noteq> [])" |
"match_interface (Some Out) (Some iface) p = ((p_oiface p) = iface)" |
"match_interface (Some Out) None p = ((p_oiface p) \<noteq> [])" |
"match_interface None (Some iface) p = ((p_iiface p = iface) \<or> (p_oiface p = iface))" |
"match_interface None None p = True"

fun match_af:: "afspec \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_af Inet _ = True" |
"match_af Inet6 _ = False" (* TODO ipv6 *)

(* uses protocol from Simple_Firewall.L4_Protocol, pf doesn't have "ProtoAny" (no protocol specified means "ProtoAny") *)
fun match_proto:: "primitive_protocol list \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_proto [] _ = False"|
"match_proto (p#ps) pkt = ((p_proto pkt = p) \<or> match_proto ps pkt)"

fun match_hosts:: "hostspec \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_hosts _ _ = True"

fun match_filteropts:: "filteropt list \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_filteropts _ _ = True"
end