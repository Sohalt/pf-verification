theory PF_PF_To_Iptables
  imports PF_Semantics_Ternary
          PF_Unknown_Match_Tacs
          PF_Primitive_Translation
          PF_Ternary_Translation
          "../PF_Primitives"
          "../PF_PrimitiveMatchers"
          Iptables_Semantics.Common_Primitive_Syntax
          Iptables_Semantics.Common_Primitive_Matcher
          Iptables_Semantics.Semantics_Ternary
          Iptables_Semantics.Unknown_Match_Tacs
begin

fun pfcp_to_iptcp :: "PF_Primitives.common_primitive \<Rightarrow> 32 common_primitive" where
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src (Hostspec (Address (IPv4 a)))) = (case prefix_match_to_CIDR a of (a,m) \<Rightarrow> (Src (IpAddrNetmask a m)))" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src (Hostspec (Address (IPv6 a)))) = undefined" |  (* has to be removed *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src (Hostspec AnyHost)) = undefined" | (* has to be translated to MatchAny first *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src (Hostspec (Route r))) = (Extra ''route'')" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src (Hostspec NoRoute)) = (Extra ''noroute'')" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src UrpfFailed) = (Extra ''urpf_failed'')" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src (Hostspec (Table _))) = undefined" | (* tables have to be translated to addresses *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst (Address (IPv4 a))) = (let (a,m) = prefix_match_to_CIDR a in (Dst (IpAddrNetmask a m)))" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst (Address (IPv6 a))) = undefined" | (* has to be removed *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst AnyHost) = undefined" |  (* has to be translated to MatchAny first *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst (Route r)) = (Extra ''route'')" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst NoRoute) = (Extra ''noroute'')" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst (Table _)) = undefined" | (* tables have to be translated to addresses *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src_OS _) = (Extra ''src_os'')" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src_Ports (PF_Primitives.L4Ports prot (Binary (RangeIncl l u)))) = (Src_Ports (L4Ports prot [(l,u)]))" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Src_Ports _) = undefined" | (* ports have to be normalized *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst_Ports (PF_Primitives.L4Ports prot (Binary (RangeIncl l u)))) = (Dst_Ports (L4Ports prot [(l,u)]))" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Dst_Ports _) = undefined" | (* ports have to be normalized *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Interface (Some (InterfaceName name)) (Some In)) = (IIface (Iface name))" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Interface (Some (InterfaceName name)) (Some Out)) = (OIface (Iface name))" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Interface _ _) = (Extra ''unsupported interface match'')" | (* iptables does not support direction *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Address_Family Inet) = undefined" | (* has to be translated *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Address_Family Inet6) = undefined" | (* has to be translated *)
"pfcp_to_iptcp (PF_Primitives.common_primitive.Protocol p) = (Prot p)" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.L4_Flags f) = (L4_Flags f)" |
"pfcp_to_iptcp (PF_Primitives.common_primitive.Extra e) = (Extra e)"

fun pfm_to_iptm :: "PF_Primitives.common_primitive match_expr \<Rightarrow> 32 common_primitive match_expr" where
"pfm_to_iptm MatchAny = MatchAny" |
"pfm_to_iptm (Match m) = (Match (pfcp_to_iptcp m))" |
"pfm_to_iptm (MatchNot m) = (MatchNot (pfm_to_iptm m))" |
"pfm_to_iptm (MatchAnd m1 m2) = (MatchAnd (pfm_to_iptm m1) (pfm_to_iptm m2))"

fun pfa_to_ipta :: "PF_Firewall_Common.action \<Rightarrow> Firewall_Common.action" where
"pfa_to_ipta Pass = Firewall_Common.action.Accept" |
"pfa_to_ipta Block = Firewall_Common.action.Drop" |
"pfa_to_ipta ActionMatch = undefined"

lemma pf_ipt_aggre_on_addr_match:
  assumes "valid_prefix pfx"
  shows "(prefix_match_semantics pfx ip) =
(ip \<in> (ipt_iprange_to_set (case prefix_match_to_CIDR pfx of
 (a, m) \<Rightarrow> (IpAddrNetmask a m))))"
  using assms by (simp add: prefix_match_to_CIDR_def prefix_match_semantics_ipset_from_netmask2)

lemmas assm_simps = no_tables_def normalized_ports_def no_ipv6_def no_af_def no_anyhost_def good_match_expr_def

lemma pf_true_ipt_not_false:
  assumes "no_tables (Match m)"
      and "normalized_ports (Match m)"
      and "no_ipv6 (Match m)"
      and "no_af (Match m)"
      and "no_anyhost (Match m)"
      and "good_match_expr ctx (Match m)"
    shows "
(ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) = TernaryTrue \<Longrightarrow>
(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) \<noteq> TernaryFalse"
proof(-)
assume prem:"(ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) = TernaryTrue"
  show ?thesis
proof(cases m)
case (Src x1)
  then show ?thesis
  proof(cases x1)
    case (Hostspec x1)
    then show ?thesis
    proof(cases x1)
      case AnyHost
      then show ?thesis using Src Hostspec assms by (auto simp:no_anyhost_def)
    next
      case NoRoute
      then show ?thesis unfolding Src Hostspec by simp
    next
      case (Address x3)
      then show ?thesis using Src Hostspec
      proof(cases x3)
        case (IPv4 x1)
        obtain addr where *:"addr = (p_src p)" by blast
        obtain a m where **: "prefix_match_to_CIDR x1 = (a,m)" by (cases "prefix_match_to_CIDR x1")
        then have "prefix_match_semantics x1 addr = (addr \<in> ipt_iprange_to_set (IpAddrNetmask a m))"
          using pf_ipt_aggre_on_addr_match[of x1] Src Hostspec Address IPv4 assms(6) by (auto simp add:good_match_expr_def)
        then show ?thesis using prem * ** Src Hostspec Address IPv4 by (simp add: tagged_packet_untag_def)
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
      then show ?thesis using Dst assms by (auto simp:no_anyhost_def)
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
          using pf_ipt_aggre_on_addr_match[of x1] Dst Address IPv4 assms(6) by (auto simp add:good_match_expr_def)
        then show ?thesis using prem * ** Dst Address IPv4 by (simp add: tagged_packet_untag_def)
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
        case (RangeIncl x11 x12)
        then show ?thesis using prem Src_Ports L4Ports Binary
          by (simp add:tagged_packet_untag_def match_port_def)
      qed (auto simp:normalized_ports_def)
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
        then show ?thesis using prem Dst_Ports L4Ports Binary
          by (simp add:tagged_packet_untag_def match_port_def)
      qed (auto simp: normalized_ports_def)
    qed
  qed
next
  case (Interface iface dir)
  then show ?thesis using prem
  proof(cases iface)
    case None
    then show ?thesis using Interface prem by auto
  next
    case *:(Some i)
    then show ?thesis
    proof(cases i)
      case (InterfaceName x1)
      then show ?thesis
      proof(cases dir)
        case None
        then show ?thesis using Interface prem by auto
      next
        case (Some a)
        then show ?thesis using * Interface InterfaceName prem
          apply(cases a) apply (auto simp:tagged_packet_untag_def) 
           apply(cases "p_iiface p = x1") apply auto apply (simp add: match_iface_eqI)
          apply(cases "p_oiface p = x1") apply auto by (simp add: match_iface_eqI)
      qed
    next
      case (InterfaceGroup x2)
      then show ?thesis using Interface * prem by auto
    qed
  qed
next
  case (Address_Family x7)
  then show ?thesis using assms by (auto simp: no_af_def)
next
  case (Protocol x8)
  then show ?thesis using prem
    by (cases x8; simp add: PF_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
next
  case (L4_Flags x9)
  then show ?thesis using prem
    by(simp add: PF_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
next
  case (Extra x10)
  then show ?thesis by simp
qed
qed

lemma pf_false_ipt_not_true:
  assumes "no_tables (Match m)"
      and "normalized_ports (Match m)"
      and "no_ipv6 (Match m)"
      and "no_af (Match m)"
      and "no_anyhost (Match m)"
      and "good_match_expr ctx (Match m)"
    shows "
(ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) = TernaryFalse \<Longrightarrow>
(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) \<noteq> TernaryTrue"
proof(-)
assume prem:"(ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) = TernaryFalse"
  show ?thesis
proof(cases m)
case (Src x1)
  then show ?thesis
  proof(cases x1)
    case (Hostspec x1)
    then show ?thesis
    proof(cases x1)
      case AnyHost
      then show ?thesis using Src Hostspec assms by (auto simp:no_anyhost_def)
    next
      case NoRoute
      then show ?thesis unfolding Src Hostspec by simp
    next
      case (Address x3)
      then show ?thesis using Src Hostspec
      proof(cases x3)
        case (IPv4 x1)
        obtain addr where *:"addr = (p_src p)" by blast
        obtain a m where **: "prefix_match_to_CIDR x1 = (a,m)" by (cases "prefix_match_to_CIDR x1")
        then have "prefix_match_semantics x1 addr = (addr \<in> ipt_iprange_to_set (IpAddrNetmask a m))"
          using pf_ipt_aggre_on_addr_match[of x1] Src Hostspec Address IPv4 assms(6) by (auto simp add:good_match_expr_def)
        then show ?thesis using prem * ** Src Hostspec Address IPv4 by (simp add: tagged_packet_untag_def)
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
      then show ?thesis using Dst assms by (auto simp:no_anyhost_def)
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
          using pf_ipt_aggre_on_addr_match[of x1] Dst Address IPv4 assms(6) by (auto simp add:good_match_expr_def)
        then show ?thesis using prem * ** Dst Address IPv4 by (simp add: tagged_packet_untag_def)
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
        case (RangeIncl x11 x12)
        then show ?thesis using prem Src_Ports L4Ports Binary
          by (simp add:tagged_packet_untag_def match_port_def)
      qed (auto simp:normalized_ports_def)
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
        then show ?thesis using prem Dst_Ports L4Ports Binary
          by (simp add:tagged_packet_untag_def match_port_def)
      qed (auto simp: normalized_ports_def)
    qed
  qed
next
  case (Interface iface dir)
  then show ?thesis using prem
  proof(cases iface)
    case None
    then show ?thesis using Interface prem by auto
  next
    case *:(Some i)
    then show ?thesis
    proof(cases i)
      case (InterfaceName x1)
      then show ?thesis
      proof(cases dir)
        case None
        then show ?thesis using Interface prem by auto
      next
        case (Some d)
        then show ?thesis using Interface InterfaceName * prem assms 
          by(cases d)
          (auto simp:good_ruleset_def good_match_expr_def match_iface_case_nowildcard tagged_packet_untag_def;
              smt ternaryvalue.distinct(1))+
      qed
    next
      case (InterfaceGroup x2)
      then show ?thesis using Interface * prem by auto
    qed
  qed
next
  case (Address_Family x7)
  then show ?thesis using assms by (auto simp: no_af_def)
next
  case (Protocol x8)
  then show ?thesis using prem
    by (cases x8; simp add: PF_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
next
  case (L4_Flags x9)
  then show ?thesis using prem
    by(simp add: PF_Matching_Ternary.matches_def matches_def tagged_packet_untag_def)
next
  case (Extra x10)
  then show ?thesis by simp
qed
qed

lemma ipt_false_pf_not_true:
  assumes "no_tables (Match m)"
      and "normalized_ports (Match m)"
      and "no_ipv6 (Match m)"
      and "no_af (Match m)"
      and "no_anyhost (Match m)"
      and "good_match_expr ctx (Match m)"
    shows "
(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) = TernaryFalse \<Longrightarrow>
(ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) \<noteq> TernaryTrue"
proof(rule classical)
  assume 1:"(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) = TernaryFalse"
  assume 2:"\<not> (ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) \<noteq> TernaryTrue"
  then show "(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) = TernaryFalse \<Longrightarrow>
             (ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) \<noteq> TernaryTrue"
    using 1 pf_true_ipt_not_false assms by auto
qed

lemma ipt_true_pf_not_false:
  assumes "no_tables (Match m)"
      and "normalized_ports (Match m)"
      and "no_ipv6 (Match m)"
      and "no_af (Match m)"
      and "no_anyhost (Match m)"
      and "good_match_expr ctx (Match m)"
    shows "
(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) = TernaryTrue \<Longrightarrow>
(ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) \<noteq> TernaryFalse"
proof(rule classical)
  assume 1:"(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) = TernaryTrue"
  assume 2:"\<not> (ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) \<noteq> TernaryFalse"
  then show "(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) = TernaryTrue \<Longrightarrow>
             (ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) \<noteq> TernaryFalse"
    using 1 pf_false_ipt_not_true assms by auto
qed

lemma pf_unknown_ipt_unknown_match:
  assumes "no_tables (Match m)"
      and "normalized_ports (Match m)"
      and "no_ipv6 (Match m)"
      and "no_af (Match m)"
      and "no_anyhost (Match m)"
      and "good_match_expr ctx (Match m)"
    shows "
(ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) (Match m))) = TernaryUnknown \<Longrightarrow>
(ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (Match (pfcp_to_iptcp m)))) = TernaryUnknown"
  using assms proof(induction m)
  case (Src x)
  then show ?case proof(cases x)
    case (Hostspec x1)
    then show ?thesis using Src Hostspec
    proof(cases x1)
      case (Address x3)
      then show ?thesis
      proof(cases x3)
        case (IPv4 x1)
        then show ?thesis using Src Hostspec Address apply auto
          using bool_to_ternary_Unknown by blast
      next
        case (IPv6 x2)
        then show ?thesis using Src Hostspec Address by (auto simp:no_ipv6_def)
      qed
    next
      case (Table x5)
      then show ?thesis using Src Hostspec apply auto
        using bool_to_ternary_Unknown by blast
    qed auto
  next
    case UrpfFailed
    then show ?thesis using Src by auto
  qed
next
  case (Src_OS x)
  then show ?case by auto
next
  case (Dst x)
  then show ?case
  proof(cases x)
    case (Address x3)
    then show ?thesis
    proof(cases x3)
      case (IPv4 x1)
      then show ?thesis using Dst Address apply auto
        using bool_to_ternary_Unknown by blast
    next
      case (IPv6 x2)
      then show ?thesis using Dst Address by (auto simp:no_ipv6_def)
    qed
  next
    case (Table x5)
    then show ?thesis using Dst apply auto
      using bool_to_ternary_Unknown by blast
  qed auto
next
  case (Src_Ports x)
  then show ?case apply (cases x) apply auto
      using bool_to_ternary_Unknown by blast
next
  case (Dst_Ports x)
  then show ?case apply (cases x) apply auto
      using bool_to_ternary_Unknown by blast
next
  case (Interface iface dir)
  then show ?case
  proof (cases iface)
    case None
    then show ?thesis using Interface by auto
  next
    case *:(Some ifspec)
    then show ?thesis
    proof(cases ifspec)
    case (InterfaceName x1)
    then show ?thesis
      proof(cases dir)
        case None
        then show ?thesis using Interface * by auto
      next
        case (Some a)
        then show ?thesis using Interface * InterfaceName Some apply(cases a) apply auto
           using bool_to_ternary_Unknown by blast+
      qed      
    next
      case (InterfaceGroup x2)
      then show ?thesis using Interface * by auto
    qed
  qed
next
  case (Address_Family x)
  then show ?case apply auto
    using bool_to_ternary_Unknown by blast
next
  case (Protocol x)
  then show ?case apply auto
    using bool_to_ternary_Unknown by blast
next
  case (L4_Flags x)
  then show ?case apply auto
    using bool_to_ternary_Unknown by blast
next
  case (Extra x)
  then show ?case by auto
qed


lemma pf_ipt_ternary_eval':
  defines "pfeval ctx p m \<equiv> (ternary_ternary_eval
         (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx)
           (tagged_packet_untag p)
           m))"
      and "ipteval p m \<equiv> ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m))"
  assumes "no_tables m"
      and "normalized_ports m"
      and "no_ipv6 m"
      and "no_af m"
      and "no_anyhost m"
      and "good_match_expr ctx m"
    shows "(pfeval ctx p m = TernaryTrue \<longrightarrow>
            ipteval p m \<noteq> TernaryFalse) \<and>
           (pfeval ctx p m = TernaryFalse \<longrightarrow>
            ipteval p m \<noteq> TernaryTrue) \<and>
           (ipteval p m = TernaryFalse \<longrightarrow> 
            pfeval ctx p m \<noteq> TernaryTrue) \<and>
           (ipteval p m = TernaryTrue \<longrightarrow> 
            pfeval ctx p m \<noteq> TernaryFalse)"
  using assms proof(induction m)
  case (Match m)
  {
    assume "pfeval ctx p (Match m) = TernaryTrue"
    then have "ipteval p (Match m) \<noteq> TernaryFalse"
      using pf_true_ipt_not_false Match by simp
  } note 1=this
  {
  assume "pfeval ctx p (Match m) = TernaryFalse"
  then have "ipteval p (Match m) \<noteq> TernaryTrue"
    using pf_false_ipt_not_true Match by simp
} note 2=this
  {
  assume "ipteval p (Match m) = TernaryTrue"
  then have "pfeval ctx p (Match m) \<noteq> TernaryFalse"
    using ipt_true_pf_not_false Match by simp
} note 3=this
  {
  assume "ipteval p (Match m) = TernaryFalse"
  then have "pfeval ctx p (Match m) \<noteq> TernaryTrue"
    using ipt_false_pf_not_true Match by simp
  } note 4=this
  show ?case (* by (rule conjI|fail,rule impI, fact) *)
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule impI) by fact
next
  case (MatchNot m)
  {
  assume "pfeval ctx p (MatchNot m) = TernaryTrue"
  then have "pfeval ctx p m = TernaryFalse"
    by (simp add: MatchNot.hyps(2) ternary_lift)
  then have "ipteval p m \<noteq> TernaryTrue" using MatchNot by (simp add: assm_simps)
  then have "ipteval p (MatchNot m) \<noteq> TernaryFalse"
    by (simp add: ipteval_def ternary_lift)
} note 1=this
  {
  assume "pfeval ctx p (MatchNot m) = TernaryFalse"
  then have "pfeval ctx p m = TernaryTrue"
    by (simp add: MatchNot.hyps(2) ternary_lift)
  then have "ipteval p m \<noteq> TernaryFalse" using MatchNot by (simp add: assm_simps)
  then have "ipteval p (MatchNot m) \<noteq> TernaryTrue"
    by (simp add: ipteval_def ternary_lift)
} note 2=this
  {
    assume "ipteval p (MatchNot m) = TernaryFalse"
    then have "ipteval p m = TernaryTrue"
      by (simp add: MatchNot.hyps(3) ternary_lift)
    then have "pfeval ctx p m \<noteq> TernaryFalse" using MatchNot by (simp add: assm_simps)
    then have "pfeval ctx p (MatchNot m) \<noteq> TernaryTrue"
      by (simp add: pfeval_def ternary_lift)
  } note 3=this
  {
    assume "ipteval p (MatchNot m) = TernaryTrue"
    then have "ipteval p m = TernaryFalse"
      by (simp add: MatchNot.hyps(3) ternary_lift)
    then have "pfeval ctx p m \<noteq> TernaryTrue" using MatchNot by (simp add: assm_simps)
    then have "pfeval ctx p (MatchNot m) \<noteq> TernaryFalse"
      by (simp add: pfeval_def ternary_lift)
  } note 4=this
  show ?case 
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule impI) by fact
next
  case (MatchAnd m1 m2)
  {
    assume "pfeval ctx p (MatchAnd m1 m2) = TernaryTrue"
    then have "pfeval ctx p m1 = TernaryTrue \<and> pfeval ctx p m2 = TernaryTrue" unfolding pfeval_def
      by (simp add: ternary_lift)
    then have "ipteval p m1 \<noteq> TernaryFalse \<and> ipteval p m2 \<noteq> TernaryFalse"
      using MatchAnd by (simp add: assm_simps)
    then have "ipteval p (MatchAnd m1 m2) \<noteq> TernaryFalse"
      by (simp add: MatchAnd.hyps(4) ternary_lift)
  } note 1=this
  {
    assume "pfeval ctx p (MatchAnd m1 m2) = TernaryFalse"
    then have "pfeval ctx p m1 = TernaryFalse \<or> pfeval ctx p m2 = TernaryFalse" unfolding pfeval_def
      by (simp add: ternary_lift)
    then have "ipteval p m1 \<noteq> TernaryTrue \<or> ipteval p m2 \<noteq> TernaryTrue"
      using MatchAnd apply (simp add: assm_simps)
      by blast
    then have "ipteval p (MatchAnd m1 m2) \<noteq> TernaryTrue"
      by (simp add: MatchAnd.hyps(4) ternary_lift)
  } note 2=this
  {
    assume "ipteval p (MatchAnd m1 m2) = TernaryTrue"
    then have "ipteval p m1 = TernaryTrue \<or> ipteval p m2 = TernaryTrue" unfolding ipteval_def
      by (simp add: ternary_lift)
    then have "pfeval ctx p m1 \<noteq> TernaryFalse \<or> pfeval ctx p m2 \<noteq> TernaryFalse"
      using MatchAnd apply (simp add: assm_simps)
      by blast
    then have "pfeval ctx p (MatchAnd m1 m2) \<noteq> TernaryFalse"
      using "2" \<open>ipteval p (MatchAnd m1 m2) = TernaryTrue\<close> by blast
  } note 3=this
  {
    assume "ipteval p (MatchAnd m1 m2) = TernaryFalse"
    then have "ipteval p m1 = TernaryFalse \<or> ipteval p m2 = TernaryFalse" unfolding ipteval_def
      by (simp add: ternary_lift)
    then have "pfeval ctx p m1 \<noteq> TernaryTrue \<or> pfeval ctx p m2 \<noteq> TernaryTrue"
      using MatchAnd apply (simp add: assm_simps)
      by blast
    then have "pfeval ctx p (MatchAnd m1 m2) \<noteq> TernaryTrue"
      using "1" \<open>ipteval p (MatchAnd m1 m2) = TernaryFalse\<close> by blast
  } note 4=this
  show ?case
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule conjI) apply(rule impI) apply fact
    apply(rule impI) by fact
next
  case MatchAny
  then show ?case by simp
qed

lemma pf_ipt_ternary_eval:
  defines "pfeval ctx p m \<equiv> (ternary_ternary_eval
         (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx)
           (tagged_packet_untag p)
           m))"
      and "ipteval p m \<equiv> ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m))"
  assumes "no_tables m"
      and "normalized_ports m"
      and "no_ipv6 m"
      and "no_af m"
      and "no_anyhost m"
      and "good_match_expr ctx m"
    shows "(pfeval ctx p m = TernaryTrue \<Longrightarrow>
            ipteval p m \<noteq> TernaryFalse)"
      and "(pfeval ctx p m = TernaryFalse \<Longrightarrow>
            ipteval p m \<noteq> TernaryTrue)"
      and "(ipteval p m = TernaryFalse \<Longrightarrow> 
            pfeval ctx p m \<noteq> TernaryTrue)"
      and "(ipteval p m = TernaryTrue \<Longrightarrow> 
            pfeval ctx p m \<noteq> TernaryFalse)"
  using pf_ipt_ternary_eval'
  by(metis assms ipteval_def pfeval_def)+

lemma pf_unknown_ipt_unknown:
  defines "pfeval ctx p m \<equiv> (ternary_ternary_eval (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx) ((tagged_packet_untag p):: 32 simple_packet) m))"
      and "ipteval p m \<equiv> (ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m)))"
  assumes "no_tables m"
      and "normalized_ports m"
      and "no_ipv6 m"
      and "no_af m"
      and "no_anyhost m"
      and "good_match_expr ctx m"
    shows "pfeval ctx p m = TernaryUnknown \<Longrightarrow> ipteval p m = TernaryUnknown"
  using assms proof(induction m)
  case (Match x)
  then show ?case using pf_unknown_ipt_unknown_match by auto
next
  case (MatchNot m)
  assume "pfeval ctx p (MatchNot m) = TernaryUnknown"
  then have "pfeval ctx p m = TernaryUnknown"
    by (simp add: MatchNot.hyps(3) eval_ternary_Not_UnknownD)
  then have "ipteval p m = TernaryUnknown" using MatchNot pf_unknown_ipt_unknown_match 
    by (auto simp: no_tables_def normalized_ports_def no_ipv6_def no_af_def no_anyhost_def good_match_expr_def)
  then show ?case
    by (simp add: MatchNot.hyps(4))
next
  case (MatchAnd m1 m2)
  assume "pfeval ctx p (MatchAnd m1 m2) = TernaryUnknown"
  then have *:"(pfeval ctx p m1 = TernaryUnknown \<and> pfeval ctx p m2 = TernaryUnknown) \<or>
            (pfeval ctx p m1 = TernaryTrue \<and> pfeval ctx p m2 = TernaryUnknown) \<or>
            (pfeval ctx p m1 = TernaryUnknown \<and> pfeval ctx p m2 = TernaryTrue)"
    by (smt MatchAnd.hyps(4) map_match_tac.simps(1) eval_ternary_simps(8) pfeval_def ternary_lift(2) ternary_lift(4) ternary_lift(6) ternary_ternary_eval.simps(1) ternaryvalue.distinct(3) ternaryvalue.distinct(5))
  { assume "(pfeval ctx p m1 = TernaryUnknown \<and> pfeval ctx p m2 = TernaryUnknown)"
  then have "(ipteval p m1 = TernaryUnknown \<and> ipteval p m2 = TernaryUnknown)" using MatchAnd pf_unknown_ipt_unknown_match
    by (auto simp: assm_simps)
  then have "ipteval p (MatchAnd m1 m2) = TernaryUnknown"
    by (simp add: MatchAnd.hyps(5)) } note 1=this
  { assume "(pfeval ctx p m1 = TernaryTrue \<and> pfeval ctx p m2 = TernaryUnknown)"
  then have "(ipteval p m1 \<noteq> TernaryFalse \<and> ipteval p m2 = TernaryUnknown)" using MatchAnd pf_unknown_ipt_unknown_match  pf_ipt_ternary_eval(1)
    by (auto simp: assm_simps)
  then have "ipteval p (MatchAnd m1 m2) = TernaryUnknown"
    by (cases "ipteval p m1") (simp add: MatchAnd.hyps(5))+ } note 2=this
  { assume "(pfeval ctx p m1 = TernaryUnknown \<and> pfeval ctx p m2 = TernaryTrue)"
  then have "(ipteval p m1 = TernaryUnknown \<and> ipteval p m2 \<noteq> TernaryFalse)" using MatchAnd pf_unknown_ipt_unknown_match  pf_ipt_ternary_eval(1)
    by (auto simp: assm_simps)
  then have "ipteval p (MatchAnd m1 m2) = TernaryUnknown"
    by (cases "ipteval p m2") (simp add: MatchAnd.hyps(5))+ } note 3=this
  show ?case using * 1 2 3 by auto
next
  case MatchAny
  then show ?case by simp
qed


lemma pf_ipt_matches:
 defines "pfeval ctx p m \<equiv> (ternary_ternary_eval
         (map_match_tac (PF_PrimitiveMatchers.common_matcher ctx)
           (tagged_packet_untag p)
           m))"
      and "ipteval p m \<equiv> ternary_ternary_eval (map_match_tac Common_Primitive_Matcher.common_matcher p (pfm_to_iptm m))"
  assumes "no_tables m"
      and "normalized_ports m"
      and "no_ipv6 m"
      and "no_af m"
      and "no_anyhost m"
      and "good_match_expr ctx m"
    shows "PF_Matching_Ternary.matches
 (PF_PrimitiveMatchers.common_matcher ctx, PF_Unknown_Match_Tacs.in_doubt_allow)
 m Pass d (tagged_packet_untag p) \<Longrightarrow>
Matching_Ternary.matches (Common_Primitive_Matcher.common_matcher, in_doubt_allow) (pfm_to_iptm m) (pfa_to_ipta Pass) p"
proof(-)
  assume prem:"PF_Matching_Ternary.matches
 (PF_PrimitiveMatchers.common_matcher ctx, PF_Unknown_Match_Tacs.in_doubt_allow)
  m Pass d (tagged_packet_untag p)"
  then show ?thesis
  proof(cases "pfeval ctx p m")
    case TernaryTrue
    then have "ipteval p m \<noteq> TernaryFalse" using pf_ipt_ternary_eval(1) assms
      by (metis PF_Firewall_Common.action.distinct(1))
    then show ?thesis unfolding PF_Matching_Ternary.matches_def Matching_Ternary.matches_def 
      by(cases "ipteval p m") (auto simp:pfeval_def ipteval_def)
  next
    case TernaryFalse
    then show ?thesis using prem unfolding pfeval_def PF_Matching_Ternary.matches_def Matching_Ternary.matches_def by auto
  next
    case TernaryUnknown
    then have "ipteval p m = TernaryUnknown" using assms pf_unknown_ipt_unknown by auto
    then show ?thesis unfolding PF_Matching_Ternary.matches_def Matching_Ternary.matches_def 
      by (auto simp:pfeval_def ipteval_def)
    qed
qed

definition pfcp_to_iptcp_rs :: "PF_Primitives.common_primitive ruleset \<Rightarrow> 32 common_primitive rule list" where
"pfcp_to_iptcp_rs = map (\<lambda>l. (case l of (PfRule r) \<Rightarrow> (Rule (pfm_to_iptm (pf_rule.get_match r)) (pfa_to_ipta (pf_rule.get_action r)))))"

definition add_default_policy :: "32 common_primitive rule list \<Rightarrow> 32 common_primitive rule list" where
"add_default_policy rs = rs @ [Rule MatchAny Firewall_Common.Accept]"

fun pf_to_ipt_v4_upper ::
"pfcontext \<Rightarrow> PF_Primitives.common_primitive ruleset \<Rightarrow> 32 common_primitive rule list" where
"pf_to_ipt_v4_upper ctx rs = 
add_default_policy
(pfcp_to_iptcp_rs 
(rev 
(remove_match_any 
(ipv4_only 
(normalize_ports_rs 
(remove_tables_rs ctx 
(remove_quick_approx 
(remove_matches 
(remove_anchors rs)))))))))"


fun pf_decision_to_ipt_decision :: "decision \<Rightarrow> state" where
"pf_decision_to_ipt_decision decision.Accept = Decision FinalAllow" |
"pf_decision_to_ipt_decision decision.Reject = Decision FinalDeny"


theorem
  assumes "PF_Predicates.wf_ruleset ctx rs"
      and "no_match_quick rs"
      and "no_unknown_anchors
            (PF_PrimitiveMatchers.common_matcher ctx, PF_Unknown_Match_Tacs.in_doubt_allow)
            rs"
  shows "pf_approx
           rs 
           (PF_PrimitiveMatchers.common_matcher ctx, PF_Unknown_Match_Tacs.in_doubt_allow)
           (tagged_packet_untag p) = decision.Accept \<Longrightarrow>
         approximating_bigstep_fun
           (Common_Primitive_Matcher.common_matcher,Unknown_Match_Tacs.in_doubt_allow)
           p 
           (pf_to_ipt_v4_upper ctx rs)
           Undecided = Decision FinalAllow"
  sorry

end
