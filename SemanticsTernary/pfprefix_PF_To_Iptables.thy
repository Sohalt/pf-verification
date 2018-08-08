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
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src_Ports (pfprefix_Primitives.L4Ports proto (Binary (RangeIncl l u)))) = (Src_Ports (L4Ports proto [(l,u)]))" |
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Src_Ports _) = undefined" | (* ports have to be normalized *)
"pfcp_to_iptcp (pfprefix_Primitives.common_primitive.Dst_Ports (pfprefix_Primitives.L4Ports proto (Binary (RangeIncl l u)))) = (Dst_Ports (L4Ports proto [(l,u)]))" |
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
    shows "
(ternary_ternary_eval (map_match_tac (pfprefix_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) =
(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m))))"
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
      then show ?thesis unfolding Src Hostspec by simp
    next
      case (Address x3)
      then show ?thesis
      proof(cases x3)
        case (IPv4 x1)
        obtain addr where *:"addr = (p_src p)" by blast
        obtain a m where **: "prefix_match_to_CIDR x1 = (a,m)" by (cases "prefix_match_to_CIDR x1")
        then have "prefix_match_semantics x1  addr = (addr \<in> ipt_iprange_to_set (IpAddrNetmask a m))"
          using pf_ipt_aggre_on_addr_match[of x1] Src Hostspec Address IPv4 assms(5) by (auto simp add:good_match_expr_def)
        then show ?thesis using * ** Src Hostspec Address IPv4 by (simp add: tagged_packet_untag_def)
      next
        case (IPv6 x2)
        then show ?thesis
          using Src Hostspec Address assms by (auto simp:no_ipv6_def)
      qed
    next
      case (Route x4)
      then show ?thesis unfolding Src Hostspec by simp
    next
      case (Table x5)
      then show ?thesis using Src Hostspec assms(1) by (auto simp:no_tables_def)
    qed
  next
    case UrpfFailed
    then show ?thesis unfolding Src by simp
  qed
next
  case (Src_OS x2)
  then show ?thesis by simp
next
  case (Dst x1)
(* almost a copy of Src *)
  then show ?thesis
    proof(cases x1)
      case AnyHost
      then show ?thesis sorry
    next
      case NoRoute
      then show ?thesis unfolding Dst by simp
    next
      case (Address x3)
      then show ?thesis
      proof(cases x3)
        case (IPv4 x1)
        obtain addr where *:"addr = (p_dst p)" by blast
        obtain a m where **: "prefix_match_to_CIDR x1 = (a,m)" by (cases "prefix_match_to_CIDR x1")
        then have "prefix_match_semantics x1  addr = (addr \<in> ipt_iprange_to_set (IpAddrNetmask a m))"
          using pf_ipt_aggre_on_addr_match[of x1] Dst Address IPv4 assms(5) by (auto simp add:good_match_expr_def)
        then show ?thesis using * ** Dst Address IPv4 by (simp add: tagged_packet_untag_def)
      next
        case (IPv6 x2)
        then show ?thesis
          using Dst Address assms by (auto simp:no_ipv6_def)
      qed
    next
      case (Route x4)
      then show ?thesis unfolding Dst by simp
    next
      case (Table x5)
      then show ?thesis using Dst assms(1) by (auto simp:no_tables_def)
    qed
next
  case (Src_Ports sp)
  then show ?thesis
  proof(cases sp)
    case (L4Ports x1 x2)
    then show ?thesis
    proof(cases x2)
      case (Unary x1)
      then show ?thesis using Src_Ports L4Ports assms by (auto simp: normalized_ports_def)
    next
      case (Binary x2)
      then show ?thesis using Src_Ports L4Ports Binary assms
      proof(cases x2) 
        case (RangeIncl l u)
        then show ?thesis using Src_Ports L4Ports Binary 
          by (simp add:tagged_packet_untag_def match_port_def)
      qed (auto simp: normalized_ports_def)
    qed
  qed
next
  case (Dst_Ports dp)
  then show ?thesis
  proof(cases dp)
    case (L4Ports x1 x2)
    then show ?thesis
    proof(cases x2)
      case (Unary x1)
      then show ?thesis using Dst_Ports L4Ports assms by (auto simp: normalized_ports_def)
    next
      case (Binary x2)
      then show ?thesis using Dst_Ports L4Ports Binary assms
      proof(cases x2) 
        case (RangeIncl l u)
        then show ?thesis using Dst_Ports L4Ports Binary 
          by (simp add:tagged_packet_untag_def match_port_def)
      qed (auto simp: normalized_ports_def)
    qed
  qed
next
  case (Interface x61 x62)
  then show ?thesis sorry
next
  case (Address_Family x7)
  then show ?thesis using assms by (auto simp: no_af_def)
next
  case (Protocol x8)
  then show ?thesis
    by (cases x8; simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
next
  case (L4_Flags x9)
  then show ?thesis
    by(simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
next
  case (Extra x10)
  then show ?thesis by simp
qed

lemma pf_ipt_ternary_eq:
  assumes "no_tables m"
      and "normalized_ports m"
      and "no_ipv6 m"
      and "no_af m"
      and "good_match_expr ctx m"
      and "a \<noteq> ActionMatch"
    shows "(ternary_ternary_eval
         (pfprefix_Matching_Ternary.map_match_tac (pfprefix_PrimitiveMatchers.common_matcher ctx)
           (tagged_packet_untag p)
           m)) =
ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m))"
  using assms proof(induction m)
  case (Match m)
  then show ?case using pf_ipt_agree_on_primitives by simp
next
  case IH:(MatchNot m)
  then show ?case by (auto simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
next
  case (MatchAnd m1 m2)
  then show ?case by (auto simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
next
  case MatchAny
  then show ?case by simp
qed

lemma pf_ipt_matches_eq: 
  assumes "no_tables m"
      and "normalized_ports m"
      and "no_ipv6 m"
      and "no_af m"
      and "good_match_expr ctx m"
      and "a \<noteq> ActionMatch"
    shows "pfprefix_Matching_Ternary.matches
 (pfprefix_PrimitiveMatchers.common_matcher ctx, pfprefix_Unknown_Match_Tacs.in_doubt_allow)
 m a d (tagged_packet_untag p) =
matches (Common_Primitive_Matcher.common_matcher, in_doubt_allow) (pfm_to_iptm m) (pfa_to_ipta a) p"
  using assms
proof(induction m rule:pfm_to_iptm.induct)
case 1
  then show ?case by(simp add: pfprefix_Matching_Ternary.matches_def matches_def)
next
case (2 m)
  then show ?case
  proof(cases "(pfprefix_PrimitiveMatchers.common_matcher ctx m (tagged_packet_untag p))")
    case TernaryTrue
    then show ?thesis using 2 pf_ipt_agree_on_primitives
      by(simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def )
  next
    case TernaryFalse
    then show ?thesis using 2 pf_ipt_agree_on_primitives
      by(simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def )
  next
    case TernaryUnknown
    then show ?thesis using 2 pf_ipt_agree_on_primitives
      apply (simp add: pfprefix_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
      by (cases a; simp)
  qed
next
  case (3 m)
  then show ?case
  proof(cases "(ternary_ternary_eval
         (pfprefix_Matching_Ternary.map_match_tac (pfprefix_PrimitiveMatchers.common_matcher ctx)
           (tagged_packet_untag p)
           m))")
    case TernaryTrue
    then have "ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m)) = TernaryTrue"
      using 3 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
    then show ?thesis using 3 TernaryTrue by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
  next
    case TernaryFalse
    then have "ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m)) = TernaryFalse"
      using 3 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
    then show ?thesis using 3 TernaryFalse by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
  next
    case TernaryUnknown
    then have "ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m)) = TernaryUnknown"
      using 3 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
    then show ?thesis using 3 TernaryUnknown apply (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
      by(cases a) auto
  qed
next
  case (4 m1 m2)
  then show ?case
  proof(cases "(ternary_ternary_eval
         (pfprefix_Matching_Ternary.map_match_tac (pfprefix_PrimitiveMatchers.common_matcher ctx)
           (tagged_packet_untag p)
           m1))")
    case m1T:TernaryTrue
    then have m1T':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m1)) = TernaryTrue"
      using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
    then show ?thesis
    proof(cases "(ternary_ternary_eval
           (pfprefix_Matching_Ternary.map_match_tac (pfprefix_PrimitiveMatchers.common_matcher ctx)
             (tagged_packet_untag p)
             m2))")
      case m2T:TernaryTrue
      then have m2T':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryTrue"
        using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
      then show ?thesis using 4 m1T m2T m1T' m2T' by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
    next
      case m2F:TernaryFalse
      then have m2F':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryFalse"
        using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
      then show ?thesis using 4 m1T m2F m1T' m2F' by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
    next
      case m2U:TernaryUnknown
      then have m2U':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryUnknown"
        using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
      then show ?thesis using 4 m1T m2U m1T' m2U' apply (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
        by(cases a) auto
    qed
    next
      case m1F:TernaryFalse
      then have m1F':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m1)) = TernaryFalse"
      using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
    then show ?thesis
    proof(cases "(ternary_ternary_eval
           (pfprefix_Matching_Ternary.map_match_tac (pfprefix_PrimitiveMatchers.common_matcher ctx)
             (tagged_packet_untag p)
             m2))")
      case m2T:TernaryTrue
      then have m2T':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryTrue"
        using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
      then show ?thesis using 4 m1F m2T m1F' m2T' by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
    next
      case m2F:TernaryFalse
      then have m2F':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryFalse"
        using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
      then show ?thesis using 4 m1F m2F m1F' m2F' by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
    next
      case m2U:TernaryUnknown
      then have m2U':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryUnknown"
        using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
      then show ?thesis using 4 m1F m2U m1F' m2U' by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
    qed
    next
      case m1U:TernaryUnknown
      then have m1U':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m1)) = TernaryUnknown"
        using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
      then show ?thesis
      proof(cases "(ternary_ternary_eval
             (pfprefix_Matching_Ternary.map_match_tac (pfprefix_PrimitiveMatchers.common_matcher ctx)
               (tagged_packet_untag p)
               m2))")
        case m2T:TernaryTrue
        then have m2T':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryTrue"
          using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
        then show ?thesis using 4 m1U m2T m1U' m2T' apply (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
          by(cases a) auto
      next
        case m2F:TernaryFalse
        then have m2F':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryFalse"
          using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
        then show ?thesis using 4 m1U m2F m1U' m2F' by (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
      next
        case m2U:TernaryUnknown
        then have m2U':"ternary_ternary_eval (Matching_Ternary.map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m2)) = TernaryUnknown"
          using 4 pf_ipt_ternary_eq by (simp add:no_tables_def normalized_ports_def no_ipv6_def no_af_def good_match_expr_def)
        then show ?thesis using 4 m1U m2U m1U' m2U' apply (simp add:pfprefix_Matching_Ternary.matches_def Matching_Ternary.matches_def)
          by(cases a) auto
      qed
    qed
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
