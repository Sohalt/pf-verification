theory PF_Example
  imports 
Example_Data
PF_PF_To_Iptables
begin

definition ipt_ruleset :: "32 Common_Primitive_Syntax.common_primitive rule list" where
"ipt_ruleset = pf_to_ipt_v4_upper pf_context pf_ruleset"

value "ipt_ruleset"

end