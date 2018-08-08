theory pfprefix_PF_To_Iptables
  imports pfprefix_Semantics_Ternary
          pfprefix_Unknown_Match_Tacs
          pfprefix_Translation
          "../pfprefix_Primitives"
          "../pfprefix_PrimitiveMatchers"
          Iptables_Semantics.Common_Primitive_Syntax
          Iptables_Semantics.Common_Primitive_Matcher
          Iptables_Semantics.Semantics_Ternary
          Iptables_Semantics.Unknown_Match_Tacs
begin

fun pfcp_to_iptcp :: "pfprefix_Primitives.common_primitive \<Rightarrow> 32 common_primitive" where
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src (Hostspec (Address (IPv4 a)))) = (case prefix_match_to_CIDR a of (a,m) \<Rightarrow> (Src (IpAddrNetmask a m)))" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src (Hostspec (Address (IPv6 a)))) = undefined" | (* TODO *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src (Hostspec AnyHost)) = undefined" | (* has to be translated to MatchAny first *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src (Hostspec (Route r))) = (Extra ''route'')" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src (Hostspec NoRoute)) = (Extra ''noroute'')" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src UrpfFailed) = (Extra ''urpf_failed'')" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src (Hostspec (Table _))) = undefined" | (* tables have to be translated to addresses *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst (Address (IPv4 a))) = (case prefix_match_to_CIDR a of (a,m) \<Rightarrow> (Dst (IpAddrNetmask a m)))" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst (Address (IPv6 a))) = undefined" | (* TODO *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst AnyHost) = undefined" |  (* has to be translated to MatchAny first *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst (Route r)) = (Extra ''route'')" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst NoRoute) = (Extra ''noroute'')" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst (Table _)) = undefined" | (* tables have to be translated to addresses *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src_OS _) = (Extra ''src_os'')" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src_Ports (Binary (RangeIncl l u))) = (Src_Ports (L4Ports TCP [(l,u)]))" | (* fixme protocol *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src_Ports _) = undefined" | (* ports have to be normalized *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst_Ports (Binary (RangeIncl l u))) = (Dst_Ports (L4Ports TCP [(l,u)]))" | (* fixme protocol *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst_Ports _) = undefined" | (* ports have to be normalized *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Interface _ _) = undefined" | (* TODO *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Address_Family Inet) = undefined" | (* TODO true *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Address_Family Inet6) = undefined" |(* TODO false *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Protocol p) = (Prot p)" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.L4_Flags f) = (L4_Flags f)" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Extra e) = (Extra e)"

fun pfm_to_iptm :: "pfprefix_Primitives.common_primitive match_expr \<Rightarrow> 32 common_primitive match_expr" where
"pfm_to_iptm MatchAny = MatchAny" |
"pfm_to_iptm (Match m) = (Match (pfcp_to_iptcp m))" |
"pfm_to_iptm (MatchNot m) = (MatchNot (pfm_to_iptm m))" |
"pfm_to_iptm (MatchAnd m1 m2) = (MatchAnd (pfm_to_iptm m1) (pfm_to_iptm m2))"

fun pfa_to_ipta :: "pfprefix_Firewall_Common.action \<Rightarrow> Firewall_Common.action" where
"pfa_to_ipta Pass = Firewall_Common.action.Accept" |
"pfa_to_ipta Block = Drop" |
"pfa_to_ipta ActionMatch = undefined"

lemma pf_ipt_aggre_on_addr_match:
  assumes "valid_prefix pfx"
  shows "(prefix_match_semantics pfx ip) = 
(ip \<in> (ipt_iprange_to_set (case prefix_match_to_CIDR pfx of
 (a, m) \<Rightarrow> (IpAddrNetmask a m))))"
  using assms by (simp add: prefix_match_to_CIDR_def prefix_match_semantics_ipset_from_netmask2)

lemma pf_ipt_agree_on_primitives: 
  assumes "no_tables (Match m)"
      and "normalized_ports (Match m)"
      and "no_ipv6 (Match m)"
      and "no_af (Match m)"
      and "good_match_expr ctx (Match m)"
      and "a \<noteq> ActionMatch"
    shows "pfprefix_Matching_Ternary.matches
 (pfprefix_PrimitiveMatchers.common_matcher ctx, pfprefix_Unknown_Match_Tacs.in_doubt_allow)
 (Match m) a d ((tagged_packet_untag p):: 32 simple_packet) =
matches (Common_Primitive_Matcher.common_matcher, in_doubt_allow) (Match (pfcp_to_iptcp m)) (pfa_to_ipta a) p"
proof(cases m)
case (Src x1)
  then show ?thesis
  proof(cases x1)
    case (Hostspec x1)
    then show ?thesis
    proof(cases x1)
      case AnyHost
      then show ?thesis sorry
    next
      case NoRoute
      then show ?thesis unfolding Src Hostspec
      apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def)
      apply(cases a) using assms by auto
    next
      case (Address x3)
      then show ?thesis
      proof(cases x3)
        case (IPv4 x1)
        obtain addr where *:"addr = (p_src p)" by blast
        obtain a m where **: "prefix_match_to_CIDR x1 = (a,m)" by (cases "prefix_match_to_CIDR x1")
        then have "prefix_match_semantics x1  addr = (addr \<in> ipt_iprange_to_set (IpAddrNetmask a m))" using pf_ipt_aggre_on_addr_match[of x1] Src Hostspec Address IPv4 assms(5) by (auto simp add:good_match_expr_def)
        then show ?thesis using * ** Src Hostspec Address IPv4 apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def) by auto
      next
        case (IPv6 x2)
        then show ?thesis
          using Src Hostspec Address assms by (auto simp:no_ipv6_def)
      qed
    next
      case (Route x4)
      then show ?thesis unfolding Src Hostspec
      apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def)
      apply(cases a) using assms by auto
    next
      case (Table x5)
      then show ?thesis using Src Hostspec assms(1) by (auto simp:no_tables_def)
    qed
  next
    case UrpfFailed
    then show ?thesis unfolding Src
    apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def)
    apply(cases a) using assms by auto
  qed
next
  case (Src_OS x2)
  then show ?thesis 
    apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def)
    apply(cases a) using assms by auto
next
  case (Dst x1)
(* almost a copy of Src *)
  then show ?thesis
    proof(cases x1)
      case AnyHost
      then show ?thesis sorry
    next
      case NoRoute
      then show ?thesis unfolding Dst
      apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def)
      apply(cases a) using assms by auto
    next
      case (Address x3)
      then show ?thesis
      proof(cases x3)
        case (IPv4 x1)
        obtain addr where *:"addr = (p_dst p)" by blast
        obtain a m where **: "prefix_match_to_CIDR x1 = (a,m)" by (cases "prefix_match_to_CIDR x1")
        then have "prefix_match_semantics x1  addr = (addr \<in> ipt_iprange_to_set (IpAddrNetmask a m))" using pf_ipt_aggre_on_addr_match[of x1] Dst Address IPv4 assms(5) by (auto simp add:good_match_expr_def)
        then show ?thesis using * ** Dst Address IPv4 apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def) by auto
      next
        case (IPv6 x2)
        then show ?thesis
          using Dst Address assms by (auto simp:no_ipv6_def)
      qed
    next
      case (Route x4)
      then show ?thesis unfolding Dst
      apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def)
      apply(cases a) using assms by auto
    next
      case (Table x5)
      then show ?thesis using Dst assms(1) by (auto simp:no_tables_def)
    qed
next
  case (Src_Ports x4)
  then show ?thesis
  proof(cases x4)
    case (Unary x1)
    then show ?thesis using Src_Ports assms by (auto simp:normalized_ports_def)
  next
    case (Binary x2)
    then show ?thesis using Src_Ports Binary assms 
    proof(cases x2)
      case (RangeIncl x11 x12)
      then show ?thesis using Src_Ports Binary
        apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
        apply(cases "(TCP = p_proto p \<and> x11 \<le> p_sport p \<and> p_sport p \<le> x12)") sorry
    qed (auto simp:normalized_ports_def)
  qed
next
  case (Dst_Ports x5)
  then show ?thesis sorry
next
  case (Interface x61 x62)
  then show ?thesis sorry
next
  case (Address_Family x7)
  then show ?thesis using assms by (auto simp: no_af_def)
next
  case (Protocol x8)
  then show ?thesis
    apply (cases x8; simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
    by (metis (full_types) Matching_Ternary.ternary_to_bool_unknown_match_tac.elims(3)
 Matching_Ternary.ternary_to_bool_unknown_match_tac.simps(2)
 bool_to_ternary_Unknown
 pfprefix_Matching_Ternary.ternary_to_bool_unknown_match_tac.elims(3)
 pfprefix_Matching_Ternary.ternary_to_bool_unknown_match_tac.simps(2))
next
  case (L4_Flags x9)
  then show ?thesis
    apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
    by (metis (full_types) Matching_Ternary.ternary_to_bool_unknown_match_tac.elims(3)
 Matching_Ternary.ternary_to_bool_unknown_match_tac.simps(2)
 bool_to_ternary_Unknown
 pfprefix_Matching_Ternary.ternary_to_bool_unknown_match_tac.elims(3)
 pfprefix_Matching_Ternary.ternary_to_bool_unknown_match_tac.simps(2))
next
  case (Extra x10)
  then show ?thesis
    apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def)
    apply(cases a) using assms by auto
qed


lemma pf_ipt_agree_on_primitives: 
  assumes "no_tables m"
      and "normalized_ports m"
      and "a \<noteq> ActionMatch"
    shows "pfprefix_Matching_Ternary.matches
 (pfprefix_PrimitiveMatchers.common_matcher ctx, pfprefix_Unknown_Match_Tacs.in_doubt_allow)
 m a d (tagged_packet_untag p) =
matches (Common_Primitive_Matcher.common_matcher, in_doubt_allow) (pfm_to_iptm m) (pfa_to_ipta a) p"
proof(induction m rule:pfm_to_iptm.induct)
case 1
  then show ?case by(simp add: pfprefix_Matching_Ternary.matches_def matches_def)
next
case (2 m)
  then show ?case sorry
next
  case (3 m)
  then show ?case sorry
next
  case (4 m1 m2)
  then show ?case sorry
qed

(*
fun pf_to_ipt :: "pfcontext \<Rightarrow> pfprefix_Primitives.common_primitive ruleset \<Rightarrow> 32 common_primitive rule list" where
"pf_to_ipt ctx rs = pfcp_to_iptcp (reverse (normalize_ports (remove_tables (remove_quick (remove_match (remove_anchors rs))))))"
*)

fun pf_decision_to_ipt_decision :: "decision \<Rightarrow> state" where
"pf_decision_to_ipt_decision Accept = Decision FinalAllow" |
"pf_decision_to_ipt_decision Reject = Decision FinalDeny"

theorem "pf_decision_to_ipt_decision
 (pf_approx rs (pfprefix_PrimitiveMatchers.common_matcher ctx, pfprefix_Unknown_Match_Tacs.in_doubt_allow) (tagged_packet_untag p)) =
approximating_bigstep_fun (common_matcher,in_doubt_allow) p (pf_to_ipt ctx rs) Undecided"
  sorry

end
