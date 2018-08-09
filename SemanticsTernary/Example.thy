theory Example
  imports pfprefix_PF_To_Iptables
          Iptables_Semantics.Semantics_Embeddings
          Simple_Firewall.Service_Matrix
          Iptables_Semantics.No_Spoof
begin

definition pf_ruleset ::"pfprefix_Primitives.common_primitive pfprefix_Firewall_Common.ruleset" where
"pf_ruleset = [
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = MatchAny\<rparr>),
(PfRule \<lparr>get_action = Block, get_quick = True, get_match = (Match (pfprefix_Primitives.common_primitive.Dst (Table ''foo'')))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (pfprefix_Primitives.Src_Ports (pfprefix_Primitives.L4Ports TCP (Unary (Lt 1000)))))
(Match (pfprefix_Primitives.Dst_Ports (pfprefix_Primitives.L4Ports TCP (Unary (Eq 22))))))\<rparr>)
]"

definition pf_context ::"pfcontext" where
"pf_context = \<lparr> get_tables = map_of [(''foo'',[TableEntryNegated (IPv4 (PrefixMatch 2 7)),TableEntry (IPv4 (PrefixMatch 4 7))])] \<rparr>"

definition preprocess :: "('i::len) common_primitive rule list \<Rightarrow> 'i common_primitive rule list" where
"preprocess rs \<equiv> upper_closure (Firewall_Common.optimize_matches abstract_for_simple_firewall (upper_closure (packet_assume_new rs)))"

definition ipt_ruleset_raw :: "32 Common_Primitive_Syntax.common_primitive rule list" where
"ipt_ruleset_raw \<equiv> pf_to_ipt pf_context pf_ruleset"

value "ipt_ruleset_raw"

value "(to_simple_firewall (preprocess ipt_ruleset_raw))"

end