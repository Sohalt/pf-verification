theory PF_Example
  imports 
Example_Data
PF_PF_To_Iptables
Iptables_Semantics.Code_Interface
begin

definition ipt_ruleset :: "32 Common_Primitive_Syntax.common_primitive rule list" where
"ipt_ruleset = pf_to_ipt_v4_upper pf_context pf_ruleset"

value "ipt_ruleset"

value "(to_simple_firewall (upper_closure
               (Firewall_Common.optimize_matches abstract_for_simple_firewall
                 (Transform.upper_closure (packet_assume_new ipt_ruleset)))))"

value "map simple_rule_ipv4_toString
          (to_simple_firewall (upper_closure
               (Firewall_Common.optimize_matches abstract_for_simple_firewall
                 (Transform.upper_closure (packet_assume_new ipt_ruleset)))))"

  definition ipassmt :: "(iface \<times> (32 word \<times> nat) list) list" where
    "ipassmt = [(Iface ''dc0'', [(ipv4addr_of_dotdecimal (192,168,0,1),24)]),
                (Iface ''dc1'', [(ipv4addr_of_dotdecimal (1,2,3,4),24)])]"

value "access_matrix_pretty_ipv4 parts_connection_ssh
              (to_simple_firewall_without_interfaces ipassmt None
                (upper_closure
                  (Firewall_Common.optimize_matches abstract_for_simple_firewall
                    (Transform.upper_closure (packet_assume_new ipt_ruleset)))))"

end