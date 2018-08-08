theory pfprefix_Firewall_Common
  imports 
"HOL-Library.Simps_Case_Conv"
Iptables_Semantics.Firewall_Common
begin
(* Block return semantically equal to Block (without return)*)
datatype action = Pass | Match | Block

definition MatchNone :: "'a match_expr" where
"MatchNone = MatchNot MatchAny"

record 'a pf_rule =
  get_action :: action
  get_quick :: bool
  get_match :: "'a match_expr"

record 'a anchor_rule =
  get_match :: "'a match_expr"

datatype 'a line =
  PfRule "'a pf_rule"
  | is_Anchor: Anchor "'a anchor_rule" "'a line list"

quickcheck_generator line constructors: PfRule

type_synonym 'a ruleset = "'a line list"

abbreviation no_anchors :: "'a ruleset \<Rightarrow> bool" where
"no_anchors ls \<equiv> (\<forall>l \<in> set ls. \<not> is_Anchor l)"

fun is_quick_rule :: "'a line \<Rightarrow> bool" where
"is_quick_rule (PfRule r) = (get_quick r)"
| "is_quick_rule _ = False"

abbreviation no_quick :: "'a ruleset \<Rightarrow> bool" where
"no_quick ls \<equiv> (\<forall> l \<in> set ls. \<not>is_quick_rule l)"

abbreviation no_match :: "'a ruleset \<Rightarrow> bool" where
"no_match ls \<equiv> (\<forall> l \<in> set ls. (case l of (PfRule r) \<Rightarrow> (pf_rule.get_action r) \<noteq> action.Match | _ \<Rightarrow> True))"

definition simple_ruleset :: "'a ruleset \<Rightarrow> bool" where
"simple_ruleset rs \<equiv> (no_anchors rs \<and> no_quick rs \<and> no_match rs)"

datatype decision =
  Accept
  | Reject

fun action_to_decision :: "action \<Rightarrow> decision \<Rightarrow> decision" where
"action_to_decision Pass _ = Accept"|
"action_to_decision Block _ = Reject"|
"action_to_decision action.Match d = d"

case_of_simps action_to_decision_cases: action_to_decision.simps

datatype decision_wrap =
  Final decision
  | is_Preliminary: Preliminary decision

fun unwrap_decision :: "decision_wrap \<Rightarrow> decision" where
"unwrap_decision (Final d) = d"
|"unwrap_decision (Preliminary d) = d"

case_of_simps unwrap_decision_cases: unwrap_decision.simps


text\<open>optimizing match expressions\<close>

fun optimize_matches_option :: "('a match_expr \<Rightarrow> 'a match_expr option) \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
  "optimize_matches_option _ [] = []" |
  "optimize_matches_option f (PfRule r#rs) = (case f (pf_rule.get_match r) of
                                               None \<Rightarrow> optimize_matches_option f rs 
                                               | Some m \<Rightarrow> (PfRule (r\<lparr>pf_rule.get_match := m\<rparr>))#optimize_matches_option f rs)"

lemma optimize_matches_option_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches_option f rs)"
  proof(induction rs rule:optimize_matches_option.induct)
  qed(simp_all add: simple_ruleset_def split: option.split)

lemma optimize_matches_option_preserves:
  assumes simple_ruleset: "simple_ruleset rs"
      and f_Some: "(\<And> r m. (PfRule r) \<in> set rs \<and> f (pf_rule.get_match r) = Some m \<Longrightarrow> P m)"
    shows "(\<forall> r \<in> set (optimize_matches_option f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) | _ \<Rightarrow> True))"
  using assms
proof(induction rs rule: optimize_matches_option.induct)
  case (1 uu)
  then show ?case by simp
next
  case (2 f r rs)
  then show ?case
  proof(cases "f (pf_rule.get_match r)")
    case None
    then show ?thesis using None 2 by (auto simp add: simple_ruleset_def)
  next
    case (Some a)
    then show ?thesis using Some 2 by (auto simp add: simple_ruleset_def)
  qed
next
  case (3 a vb vc va)
  then show ?case by (auto simp add: simple_ruleset_def)
qed


(*
lemma optimize_matches_option_preserves':
  "\<forall> m \<in> set rs. P (get_match m) \<Longrightarrow> \<forall>m. P m \<longrightarrow> (\<forall>m'. f m = Some m' \<longrightarrow> P m') \<Longrightarrow> \<forall>m \<in> set (optimize_matches_option f rs). P (get_match m)"
  using optimize_matches_option_preserves[simplified] by metis
*)
lemma optimize_matches_option_append: 
  assumes "simple_ruleset rs1"
      and "simple_ruleset rs2"
    shows "optimize_matches_option f (rs1@rs2) = optimize_matches_option f rs1 @ optimize_matches_option f rs2"
  using assms by(induction rs1 rule: optimize_matches_option.induct;auto simp add: simple_ruleset_def split: option.split)


definition optimize_matches :: "('a match_expr \<Rightarrow> 'a match_expr) \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
  "optimize_matches f rs =  optimize_matches_option (\<lambda>m. (if matcheq_matchNone (f m) then None else Some (f m))) rs"

lemma optimize_matches_append:
  assumes "simple_ruleset rs1"
      and "simple_ruleset rs2"
    shows "optimize_matches f (rs1@rs2) = optimize_matches f rs1 @ optimize_matches f rs2"
  using assms by(simp add: optimize_matches_def optimize_matches_option_append)

lemma optimize_matches_preserves:
  assumes "simple_ruleset rs"
  shows  "(\<And> r. (PfRule r) \<in> set rs \<Longrightarrow> P (f (pf_rule.get_match r))) \<Longrightarrow>
    \<forall> r \<in> set (optimize_matches f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) | _ \<Rightarrow> True)"
  using assms
  unfolding optimize_matches_def
  apply(rule optimize_matches_option_preserves)
  by(auto split: if_split_asm)

lemma optimize_matches_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches f rs)"
  by(simp add: optimize_matches_def optimize_matches_option_simple_ruleset)



fun optimize_matches_a :: "(action \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr) \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
"optimize_matches_a _ [] = []" |
"optimize_matches_a f (PfRule r#rs) = (PfRule (r\<lparr>pf_rule.get_match := f (pf_rule.get_action r) (pf_rule.get_match r)\<rparr>))#optimize_matches_a f rs"

lemma optimize_matches_a_simple_ruleset: "simple_ruleset rs \<Longrightarrow> simple_ruleset (optimize_matches_a f rs)"
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
  proof(cases a)
    case (PfRule x1)
    then have "simple_ruleset rs" using Cons(2) by (simp add: simple_ruleset_def)
    then show ?thesis 
      (* TODO make less ugly *)
      unfolding PfRule using Cons apply (simp add: simple_ruleset_def) apply auto
      using PfRule is_quick_rule.simps(1) apply blast
      by (simp add: PfRule)
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons(2) by (auto simp add: simple_ruleset_def)
  qed
qed

lemma optimize_matches_a_simple_ruleset_eq:
  "simple_ruleset rs \<Longrightarrow> (\<And> m a. a = Pass \<or> a = Block \<Longrightarrow> f1 a m = f2 a m) \<Longrightarrow> optimize_matches_a f1 rs = optimize_matches_a f2 rs"
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
  proof(cases a)
    case (PfRule x1)
    then show ?thesis using Cons by (auto simp add:simple_ruleset_def) (cases "get_action x1";auto)
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons by (auto simp add:simple_ruleset_def)
  qed
qed

lemma optimize_matches_a_preserves:
  assumes "simple_ruleset rs"
  shows "(\<And> r. (PfRule r) \<in> set rs \<Longrightarrow> P (f (pf_rule.get_action r) (pf_rule.get_match r)))
    \<Longrightarrow> \<forall> r \<in> set (optimize_matches_a f rs). (case r of (PfRule r) \<Rightarrow> P (pf_rule.get_match r) | _ \<Rightarrow> True)"
  using assms
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case using Cons by (cases a; auto simp add: simple_ruleset_def)
qed


end