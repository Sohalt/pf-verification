theory PF_Closures
imports
PF_Firewall_Common
PF_Primitive_Matchers
begin
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

lemma ports_neq_TernaryUnknown:
  "(\<exists>p. common_matcher ctx (Src_Ports ps) p \<noteq> TernaryUnknown)"
  "(\<exists>p. common_matcher ctx (Dst_Ports ps) p \<noteq> TernaryUnknown)"
  by(case_tac [!] ps) (simp_all add: bool_to_ternary_Unknown)

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
      simp: remove_unknowns_generic_simps2 bool_to_ternary_Unknown helper_neq_TernaryUnknown ports_neq_TernaryUnknown
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
      simp: remove_unknowns_generic_simps2 bool_to_ternary_Unknown helper_neq_TernaryUnknown ports_neq_TernaryUnknown
      split: action.splits decision.splits)
end