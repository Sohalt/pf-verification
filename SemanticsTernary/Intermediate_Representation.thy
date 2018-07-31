theory Intermediate_Representation
  imports
    "../Firewall_Common"
    IP_Addresses.WordInterval
    Simple_Firewall.L4_Protocol
    Simple_Firewall.Simple_Packet
    Iptables_Semantics.Ternary
begin

context
  notes [[typedef_overloaded]]
begin
datatype iface =
Iface "string"
| IfaceWildcard

datatype 'i intermediate_primitive =
Src "'i wordinterval"
| Dst "'i wordinterval"
| Src_Ports "16 wordinterval"
| Dst_Ports "16 wordinterval"
| IIface iface
| OIface iface
| Protocol primitive_protocol
| Unknown
end

fun intermediate_matcher :: "'i::len intermediate_primitive \<Rightarrow> 'i simple_packet \<Rightarrow> ternaryvalue" where
"intermediate_matcher (Src a) p = bool_to_ternary (wordinterval_element (p_src p) a)" |
"intermediate_matcher (Dst a) p = bool_to_ternary (wordinterval_element (p_dst p) a)" |
"intermediate_matcher (Src_Ports port) p = bool_to_ternary (wordinterval_element (p_sport p) port)" |
"intermediate_matcher (Dst_Ports port) p = bool_to_ternary (wordinterval_element (p_dport p) port)" |
"intermediate_matcher (IIface (Iface i)) p = bool_to_ternary ((p_iiface p) = i)" |
"intermediate_matcher (IIface IfaceWildcard) p = bool_to_ternary ((p_iiface p) \<noteq> '''')" |
"intermediate_matcher (OIface (Iface i)) p = bool_to_ternary ((p_oiface p) = i)" |
"intermediate_matcher (OIface IfaceWildcard) p = bool_to_ternary ((p_oiface p) \<noteq> '''')" |
"intermediate_matcher (Protocol proto) p = bool_to_ternary ((p_proto p) = proto)" |
"intermediate_matcher Unknown _ = TernaryUnknown"

end