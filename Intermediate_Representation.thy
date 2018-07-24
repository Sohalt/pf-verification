theory Intermediate_Representation
  imports
    Firewall_Common
    IP_Addresses.WordInterval
    Simple_Firewall.L4_Protocol
    Simple_Firewall.Simple_Packet
    Iptables_Semantics.Ternary
begin

context
  notes [[typedef_overloaded]]
begin
datatype 'i intermediate_primitive =
Src "'i wordinterval"
| Dst "'i wordinterval"
| Src_Port "16 wordinterval"
| Dst_Port "16 wordinterval"
| IIface "string"
| OIface "string"
| Protocol primitive_protocol
| Unknown
end

fun itermediate_matcher :: "'i::len intermediate_primitive \<Rightarrow> 'i simple_packet \<Rightarrow> ternaryvalue" where
"itermediate_matcher (Src a) p = bool_to_ternary (wordinterval_element (p_src p) a)" |
"itermediate_matcher (Dst a) p = bool_to_ternary (wordinterval_element (p_dst p) a)" |
"itermediate_matcher (Src_Port port) p = bool_to_ternary (wordinterval_element (p_sport p) port)" |
"itermediate_matcher (Dst_Port port) p = bool_to_ternary (wordinterval_element (p_dport p) port)" |
"itermediate_matcher (IIface i) p = bool_to_ternary ((p_iiface p) = i)" |
"itermediate_matcher (OIface i) p = bool_to_ternary ((p_oiface p) = i)" |
"itermediate_matcher (Protocol proto) p = bool_to_ternary ((p_proto p) = proto)" |
"itermediate_matcher Unknown _ = TernaryUnknown"

end