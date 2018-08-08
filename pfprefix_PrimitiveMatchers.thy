theory pfprefix_PrimitiveMatchers
  imports pfprefix_Primitives
          Simple_Firewall.Simple_Packet
          Iptables_Semantics.Ternary
          pfprefix_Tables
          pfprefix_Firewall_Common
          "SemanticsTernary/pfprefix_Unknown_Match_Tacs"
begin

fun match_interface :: "pfcontext \<Rightarrow> ifspec option \<Rightarrow> direction option \<Rightarrow> 32 simple_packet \<Rightarrow> ternaryvalue" where
"match_interface ctx (Some (InterfaceGroup _)) _ _ = TernaryUnknown" |
"match_interface _ (Some (InterfaceName iface)) None p = bool_to_ternary (((p_iiface p) = iface) \<or> ((p_oiface p) = iface))" |
"match_interface _ (Some (InterfaceName iface)) (Some In) p = bool_to_ternary ((p_iiface p) = iface)" |
"match_interface _ (Some (InterfaceName iface)) (Some Out) p = bool_to_ternary ((p_oiface p) = iface)" |
"match_interface _ None (Some In) p = bool_to_ternary ((p_iiface p) \<noteq> '''')" |
"match_interface _ None (Some Out) p = bool_to_ternary ((p_oiface p) \<noteq> '''')" |
"match_interface _ None None _ = TernaryFalse"

fun match_af:: "afspec \<Rightarrow> 'i::len0 simple_packet \<Rightarrow> bool" where
"match_af Inet p \<longleftrightarrow> len_of TYPE ('i) = 32"
|"match_af Inet6 p \<longleftrightarrow> len_of TYPE ('i) = 128"

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
"match_binary_op (RangeComp l u) x = (l > x \<or> x > u)"

fun match_op :: "'i::ord opspec \<Rightarrow> 'i \<Rightarrow> bool" where
"match_op (Unary operator) x = match_unary_op operator x" |
"match_op (Binary operator) x = match_binary_op operator x"

definition match_port :: "16 word opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port operator port = match_op operator port"


(* TODO ipv6 *)
fun match_hosts :: "pfcontext \<Rightarrow> hostspec \<Rightarrow> 32 word \<Rightarrow> ternaryvalue" where
"match_hosts _ AnyHost _ = bool_to_ternary True" |
"match_hosts _ (Address addr) p_addr =
(case addr of
 (IPv4 a) \<Rightarrow> bool_to_ternary (prefix_match_semantics a p_addr)
| (IPv6 _) \<Rightarrow> TernaryFalse)"|
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
"common_matcher ctx (Interface interface direction) p = match_interface ctx interface direction p"|
"common_matcher _ (Address_Family af) p = bool_to_ternary (match_af af p)"|
"common_matcher _ (Protocol proto) p = bool_to_ternary (match_proto proto (p_proto p))"|
"common_matcher _ (L4_Flags flags) p = bool_to_ternary (match_tcp_flags flags  (p_tcp_flags p))"|
"common_matcher _ (Extra _) _ = TernaryUnknown"

subsection\<open>Abstracting over unknowns\<close>
  text\<open>remove match expressions which evaluate to @{const TernaryUnknown}\<close>
  fun upper_closure_matchexpr :: "action \<Rightarrow> decision \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
    "upper_closure_matchexpr _ _ MatchAny = MatchAny" |
    "upper_closure_matchexpr a d (Match (Extra _)) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (Match (Src_OS _)) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (Match (Interface (Some (InterfaceGroup _)) _)) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (Match (Src (Hostspec NoRoute))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (Match (Src (Hostspec (Route _)))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (Match (Src UrpfFailed)) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (Match (Dst NoRoute)) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (Match (Dst (Route _))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr _ _ (Match m) = Match m" |
    "upper_closure_matchexpr a d (MatchNot (Match (Extra _))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (Match (Src_OS _))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (Match (Interface (Some (InterfaceGroup _)) _))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (Match (Src (Hostspec NoRoute)))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (Match (Src (Hostspec (Route _))))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (Match (Src UrpfFailed))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (Match (Dst NoRoute))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (Match (Dst (Route _)))) = (case a of Pass \<Rightarrow> MatchAny | Block \<Rightarrow> MatchNot MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchAny | Reject \<Rightarrow> MatchNot MatchAny))" |
    "upper_closure_matchexpr a d (MatchNot (MatchNot m)) = upper_closure_matchexpr a d m" |
    "upper_closure_matchexpr a d (MatchNot (MatchAnd m1 m2)) =
      (let m1' = upper_closure_matchexpr a d (MatchNot m1); m2' = upper_closure_matchexpr a d (MatchNot m2) in
      (if m1' = MatchAny \<or> m2' = MatchAny
       then MatchAny
       else
          if m1' = MatchNot MatchAny then m2' else
          if m2' = MatchNot MatchAny then m1'
       else
          MatchNot (MatchAnd (MatchNot m1') (MatchNot m2')))
         )" |
    "upper_closure_matchexpr _ _ (MatchNot m) = MatchNot m" |
    "upper_closure_matchexpr a d (MatchAnd m1 m2) = MatchAnd (upper_closure_matchexpr a d m1) (upper_closure_matchexpr a d m2)"

lemma helper_neq_TernaryUnknown:
  "(\<exists>p. (case ip of IPv4 a \<Rightarrow> bool_to_ternary (prefix_match_semantics a (p_src p)) | IPv6 x \<Rightarrow> TernaryFalse) \<noteq> TernaryUnknown)"
  "(\<exists>p. (case ip of IPv4 a \<Rightarrow> bool_to_ternary (prefix_match_semantics a (p_dst p)) | IPv6 x \<Rightarrow> TernaryFalse) \<noteq> TernaryUnknown)"
  "(\<exists>p. match_interface ctx None dir p \<noteq> TernaryUnknown)"
  "(\<exists>p. match_interface ctx (Some (InterfaceName ifname)) dir p \<noteq> TernaryUnknown)"
     apply (case_tac [!] ip, case_tac [!] dir) apply(simp_all add:bool_to_ternary_Unknown)
     apply (smt bool_to_ternary_Unknown match_interface.elims option.discI ternaryvalue.distinct(5))
    apply (smt bool_to_ternary_Unknown match_interface.elims option.discI ternaryvalue.distinct(5))
   apply (metis (full_types) bool_to_ternary_Unknown direction.exhaust match_interface.simps(3) match_interface.simps(4))
  by (metis (full_types) bool_to_ternary_Unknown direction.exhaust match_interface.simps(3) match_interface.simps(4))

  lemma upper_closure_matchexpr_generic:
    "remove_unknowns_generic (common_matcher ctx, in_doubt_allow) a d m = upper_closure_matchexpr a d m"
by (induction a d m rule: upper_closure_matchexpr.induct)
   (auto
      simp: remove_unknowns_generic_simps2 bool_to_ternary_Unknown helper_neq_TernaryUnknown
      split: action.splits decision.splits)

    fun lower_closure_matchexpr :: "action \<Rightarrow> decision \<Rightarrow> common_primitive match_expr \<Rightarrow> common_primitive match_expr" where
    "lower_closure_matchexpr _ _ MatchAny = MatchAny" |
    "lower_closure_matchexpr a d (Match (Extra _)) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (Match (Src_OS _)) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (Match (Interface (Some (InterfaceGroup _)) _)) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (Match (Src (Hostspec NoRoute))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (Match (Src (Hostspec (Route _)))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (Match (Src UrpfFailed)) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (Match (Dst NoRoute)) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (Match (Dst (Route _))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr _ _ (Match m) = Match m" |
    "lower_closure_matchexpr a d (MatchNot (Match (Extra _))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (Match (Src_OS _))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (Match (Interface (Some (InterfaceGroup _)) _))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (Match (Src (Hostspec NoRoute)))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (Match (Src (Hostspec (Route _))))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (Match (Src UrpfFailed))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (Match (Dst NoRoute))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (Match (Dst (Route _)))) = (case a of Pass \<Rightarrow> MatchNot MatchAny | Block \<Rightarrow> MatchAny | ActionMatch \<Rightarrow> (case d of Accept \<Rightarrow> MatchNot MatchAny | Reject \<Rightarrow> MatchAny))" |
    "lower_closure_matchexpr a d (MatchNot (MatchNot m)) = lower_closure_matchexpr a d m" |
    "lower_closure_matchexpr a d (MatchNot (MatchAnd m1 m2)) =
      (let m1' = lower_closure_matchexpr a d (MatchNot m1); m2' = lower_closure_matchexpr a d (MatchNot m2) in
      (if m1' = MatchAny \<or> m2' = MatchAny
       then MatchAny
       else
          if m1' = MatchNot MatchAny then m2' else
          if m2' = MatchNot MatchAny then m1'
       else
          MatchNot (MatchAnd (MatchNot m1') (MatchNot m2')))
         )" |
    "lower_closure_matchexpr _ _ (MatchNot m) = MatchNot m" |
    "lower_closure_matchexpr a d (MatchAnd m1 m2) = MatchAnd (lower_closure_matchexpr a d m1) (lower_closure_matchexpr a d m2)"

  lemma lower_closure_matchexpr_generic:
    "remove_unknowns_generic (common_matcher ctx, in_doubt_deny) a d m = lower_closure_matchexpr a d m"
    by (induction a d m rule: lower_closure_matchexpr.induct)
     (auto
      simp: remove_unknowns_generic_simps2 bool_to_ternary_Unknown helper_neq_TernaryUnknown
      split: action.splits decision.splits)
end