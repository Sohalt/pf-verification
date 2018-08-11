theory pfprefix_Ternary_Translation
  imports "../pfprefix_Pf_To_Simple_Firewall"
          "../pfprefix_PrimitiveMatchers"
          pfprefix_Semantics_Ternary
          pfprefix_Unknown_Match_Tacs
begin

lemma filter_approx_to_pf_approx:
  assumes "\<forall> d. (filter_approx l1 \<gamma> p d = filter_approx l2 \<gamma> p d)"
  shows "pf_approx l1 \<gamma> p = pf_approx l2 \<gamma> p" unfolding pf_approx_def using assms by simp


lemma and_each_false[simp]:
  assumes "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m)) = TernaryFalse"
  shows "filter_approx (and_each m l) \<gamma> p d = d"
  using assms
  by (induction l)
     (auto split:line.splits decision_wrap.splits
           simp:filter_approx_cases and_line_cases matches_def eval_ternary_simps_simple(3))

lemma and_each_true[simp]:
  assumes "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m)) = TernaryTrue"
  shows "filter_approx (and_each m l) \<gamma> p d = filter_approx l \<gamma> p d"
  using assms
proof(induction l arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by (cases d;cases a) 
       (auto simp:matches_def eval_ternary_simps_simple(1))
qed

fun all_AnchorRules_P :: "('a anchor_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_AnchorRules_P P rs = (\<forall> l \<in> set rs. (case l of (Anchor r b) \<Rightarrow> P r \<and> all_AnchorRules_P P b | _ \<Rightarrow> True))"

fun all_AnchorRules_P' :: "('a anchor_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_AnchorRules_P' _ [] \<longleftrightarrow> True" |
"all_AnchorRules_P' P ((PfRule r)#ls) \<longleftrightarrow> all_AnchorRules_P' P ls" |
"all_AnchorRules_P' P ((Anchor r b)#ls) \<longleftrightarrow> P r \<and> all_AnchorRules_P' P b \<and> all_AnchorRules_P' P ls"

lemma "all_AnchorRules_P P l= all_AnchorRules_P' P l"
  by (induction P l rule: all_AnchorRules_P'.induct) auto

lemma all_AnchorRules_append[simp]:
  "all_AnchorRules_P P (xs @ ys) \<longleftrightarrow> all_AnchorRules_P P xs \<and> all_AnchorRules_P P ys"
  by (induction P xs rule: all_AnchorRules_P.induct) auto

definition no_anchors' :: "'a ruleset \<Rightarrow> bool" where
"no_anchors' rs = all_AnchorRules_P (\<lambda>r. False) rs"

lemma no_anchors_no_anchors'_eq:
 "no_anchors rs \<longleftrightarrow> no_anchors' rs"
  unfolding no_anchors'_def
  by (induction rs) (auto split:line.splits)


definition no_unknown_anchors :: "('a,'p) match_tac \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"no_unknown_anchors \<gamma> rs = all_AnchorRules_P
 (\<lambda>r. (\<forall> p. ternary_ternary_eval (map_match_tac (fst \<gamma>) p (anchor_rule.get_match r)) \<noteq> TernaryUnknown))
 rs"


fun all_PfRules_P :: "('a pf_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_PfRules_P P rs = (\<forall> l \<in> set rs. (case l of (PfRule r) \<Rightarrow> P r | (Anchor r b) \<Rightarrow> all_PfRules_P P b))"

fun all_PfRules_P' :: "('a pf_rule \<Rightarrow> bool) \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"all_PfRules_P' _ [] \<longleftrightarrow> True" |
"all_PfRules_P' P ((PfRule r)#ls) \<longleftrightarrow> P r \<and> all_PfRules_P' P ls" |
"all_PfRules_P' P ((Anchor r b)#ls) \<longleftrightarrow> all_PfRules_P' P b \<and> all_PfRules_P' P ls"

lemma "all_PfRules_P P l= all_PfRules_P' P l"
  by (induction P l rule: all_PfRules_P'.induct) auto

lemma all_PfRules_append[simp]:
  "all_PfRules_P P (xs @ ys) \<longleftrightarrow> all_PfRules_P P xs \<and> all_PfRules_P P ys"
  by (induction P xs rule: all_PfRules_P.induct) auto

definition no_match_quick :: "'a ruleset \<Rightarrow> bool" where
"no_match_quick rs = all_PfRules_P (\<lambda>r. \<not>((pf_rule.get_action r) = ActionMatch \<and> pf_rule.get_quick r)) rs"

(* remove anchors *)

(* remove_anchors implementation and remove_anchors_ok in Pf_To_SimpleFirewall *)

lemma remove_anchors'_preserves_semantics :
  assumes "no_match_quick rs"
      and "no_unknown_anchors (\<alpha>, in_doubt_allow) rs"
    shows "pf_approx (remove_anchors' rs) (\<alpha>, in_doubt_allow) p =
           pf_approx rs (\<alpha>, in_doubt_allow) p"
proof(-)
  have "filter_approx rs (\<alpha>, in_doubt_allow) p d =
        filter_approx (remove_anchors' rs) (\<alpha>, in_doubt_allow) p d" for d 
    using assms
  proof(induction rs arbitrary:d rule:remove_anchors'.induct)
    case 1
    then show ?case by simp
  next
    case (2 r l rs)
    then show ?case
    proof(cases "(ternary_ternary_eval (map_match_tac \<alpha> p (anchor_rule.get_match r)))")
      case TernaryTrue
      then show ?thesis using 2 apply (auto simp add: filter_approx_chain)
        by (cases d;auto simp add:matches_def no_match_quick_def no_unknown_anchors_def)
    next
      case TernaryFalse
      then show ?thesis using 2 apply (auto simp add: filter_approx_chain)
        by (cases d;auto simp add:matches_def no_match_quick_def no_unknown_anchors_def)
    next
      case TernaryUnknown
      then show ?thesis using 2(4) by (auto simp:no_unknown_anchors_def)
    qed
  next
    case (3 v rs)
    then show ?case apply (simp add:no_match_quick_def no_unknown_anchors_def)
      by (metis (no_types, hide_lams) append_Cons append_Nil filter_approx_chain)
  qed
  then show ?thesis by (simp add: filter_approx_to_pf_approx)
qed

(* lemma and_each_preserves_action_and_quick[simp,intro]:
  assumes "all_PfRules_P (\<lambda>r. P (pf_rule.get_action r) (pf_rule.get_quick r)) ls"
  shows "all_PfRules_P (\<lambda>r. P (pf_rule.get_action r) (pf_rule.get_quick r)) (and_each m ls)"
  using assms proof(induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons l ls)
  then show ?case by(cases l;auto)
qed *)

lemma and_each_preserves_no_match_quick[simp,intro]:
  assumes "no_match_quick l"
  shows "no_match_quick (and_each m l)"
  using assms
proof(induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by (cases a) (auto simp:no_match_quick_def)
qed

lemma no_match_quick_append[simp]:
  "no_match_quick (l1@l2) \<longleftrightarrow> no_match_quick l1 \<and> no_match_quick l2"
  by (auto simp:no_match_quick_def)

lemma remove_anchors'_preserves_no_match_quick:
  assumes "no_match_quick l"
  shows "no_match_quick (remove_anchors' l)"
  using assms
proof(induction l rule:remove_anchors'.induct)
  case 1
  then show ?case by simp
next
  case (2 r l rs)
  have "no_match_quick (remove_anchors' l)" using 2(1) 2(3) by (simp add:no_match_quick_def)
  then have *:"no_match_quick (and_each (anchor_rule.get_match r) (remove_anchors' l))" by simp
  have "no_match_quick (remove_anchors' rs)" using 2(2) 2(3) by (simp add:no_match_quick_def)
  then show ?case using * by simp
next
  case (3 v rs)
  then show ?case by (simp add:no_match_quick_def)
qed

  
(* helpers for remove quick *)

lemma remove_suffix[simp]:
  assumes "\<not>matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) (unwrap_decision (filter_approx l \<gamma> p d)) p"
  shows "filter_approx (l@[(PfRule r)]) \<gamma> p d = filter_approx l \<gamma> p d"
  using assms by (cases "filter_approx l \<gamma> p d") (simp add: filter_approx_chain)+

lemma no_quick_preliminary:
  assumes "no_quick rules"
      and "no_anchors rules" (* not necessary but makes things easier *)
    shows "is_Preliminary (filter_approx rules \<gamma> p (Preliminary d))"
  using assms by (induction rules arbitrary: d) (auto split:line.splits simp:filter_approx_cases)

(* remove quick *)

fun remove_quick_approx :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick_approx [] = []" |
"remove_quick_approx ((PfRule r)#ls) =
(if (get_quick r)
  then (remove_quick_approx ls) @ [PfRule (r\<lparr>get_quick := False\<rparr>)]
  else (PfRule r)#(remove_quick_approx ls))"

lemma remove_quick_approx_ok:
  assumes "no_anchors rules"
  shows "no_quick (remove_quick_approx rules)"
    using assms by (induction rules rule:remove_quick_approx.induct) auto

lemma remove_quick_approx_preserves_no_anchors:
  assumes "no_anchors rules"
  shows "no_anchors (remove_quick_approx rules)"
  using assms by (induction rules rule:remove_quick_approx.induct) simp+

lemma remove_quick_approx_preserves_no_match:
  assumes "no_anchors rules"
      and "no_match rules"
    shows "no_match (remove_quick_approx rules)"
  using assms
  by (induction rules rule:remove_quick_approx.induct) simp+

lemma remove_quick_approx_preserves_semantics:
  assumes "no_anchors rules"
      and "no_match rules"
      and "good_matcher \<gamma>"
    shows "pf_approx rules \<gamma> p = pf_approx (remove_quick_approx rules) \<gamma> p"
proof(-)
  from assms have "(unwrap_decision (filter_approx rules \<gamma> p d) =
                    unwrap_decision (filter_approx (remove_quick_approx rules) \<gamma> p d))" for d
  proof(induction rules arbitrary:d rule:remove_quick_approx.induct)
  case 1
  then show ?case by simp
  next
    case (2 r ls)
    then show ?case
    proof(cases d)
      case (Final x1)
      then show ?thesis by auto
    next
      case (Preliminary x2)
      have "no_anchors (remove_quick_approx ls)"
        using 2 by (simp add:remove_quick_approx_preserves_no_anchors)
      moreover have "no_quick (remove_quick_approx ls)"
        using 2 by (simp add:remove_quick_approx_ok)
      ultimately have prem:"is_Preliminary(filter_approx (remove_quick_approx ls) \<gamma> p (Preliminary x2))"
        using no_quick_preliminary by metis
      show ?thesis
      proof(cases "get_quick r")
        case quick:True
        then show ?thesis
        proof(cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p (pf_rule.get_match r)))")
          case TernaryTrue
          then have "(filter_approx (PfRule r # ls) \<gamma> p (Preliminary x2)) =
                      Final (action_to_decision (pf_rule.get_action r) x2)"
            (is "?dw = Final ?d")
            using quick TernaryTrue by (simp add:matches_def)
          then have res1: "unwrap_decision ?dw = ?d" by simp
          have "filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) = 
                filter_approx [PfRule (r\<lparr>get_quick := False\<rparr>)] \<gamma> p (filter_approx (remove_quick_approx ls) \<gamma> p (Preliminary x2))"
            using quick by (simp add:filter_approx_chain)
          then have "\<exists> d. filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) = 
                          filter_approx [PfRule (r\<lparr>get_quick := False\<rparr>)] \<gamma> p (Preliminary d)" using prem is_Preliminary_def by auto
          then obtain d' where "filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) = 
                               filter_approx [PfRule (r\<lparr>get_quick := False\<rparr>)] \<gamma> p (Preliminary d')" by blast
          then have "filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) =
                     Preliminary (action_to_decision (pf_rule.get_action r) d')"
            (is "?dw = Preliminary ?d")
            using TernaryTrue by (simp add:matches_def)
          then have res2:"unwrap_decision ?dw = ?d" by simp
          show ?thesis using Preliminary quick TernaryTrue res1 res2 2(4)
            by (auto split:action.splits simp:matches_def action_to_decision_cases)
        next
          case TernaryFalse
          then have res1:"filter_approx (PfRule r # ls) \<gamma> p (Preliminary x2) =
                     filter_approx ls \<gamma> p (Preliminary x2)" by (simp add:matches_def)
          have res2:"filter_approx ((remove_quick_approx ls)@[PfRule (r\<lparr>get_quick := False\<rparr>)]) \<gamma> p (Preliminary x2) =
                     filter_approx (remove_quick_approx ls) \<gamma> p (Preliminary x2)"
            using TernaryFalse by (simp add:matches_def)
          show ?thesis using Preliminary TernaryFalse res1 res2 2
            by (auto split:action.splits simp:matches_def action_to_decision_cases)
        next
          case TernaryUnknown
          then show ?thesis
          proof(cases "(snd \<gamma>) (pf_rule.get_action r) x2 p")
            case True
            then have "(filter_approx (PfRule r # ls) \<gamma> p (Preliminary x2)) = Final (action_to_decision (pf_rule.get_action r) x2)" (is "?dw = Final ?d")
              using quick TernaryUnknown by (simp add:matches_def)
            then have res1: "unwrap_decision ?dw = ?d" by simp
            have "filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) = 
                  filter_approx [PfRule (r\<lparr>get_quick := False\<rparr>)] \<gamma> p (filter_approx (remove_quick_approx ls) \<gamma> p (Preliminary x2))"
              using quick by (simp add:filter_approx_chain)
            then have "\<exists> d. filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) = 
                          filter_approx [PfRule (r\<lparr>get_quick := False\<rparr>)] \<gamma> p (Preliminary d)" using prem is_Preliminary_def by auto
            then obtain d' where "filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) = 
                                  filter_approx [PfRule (r\<lparr>get_quick := False\<rparr>)] \<gamma> p (Preliminary d')" by blast
            moreover have "(snd \<gamma>) (pf_rule.get_action r) d' p"
              using True 2(4) 2(5) unfolding good_matcher_def apply(auto split:action.splits) by metis
            ultimately have "filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2) =
                       Preliminary (action_to_decision (pf_rule.get_action r) d')" (is "?dw = Preliminary ?d")
            using TernaryUnknown True 2 by (simp add:matches_def)
          then have res2:"unwrap_decision ?dw = ?d" by simp
          show ?thesis using Preliminary True TernaryUnknown res1 res2 2(4) by (auto split:action.splits simp:matches_def action_to_decision_cases)
          next
            case False
            then have res1: "unwrap_decision (filter_approx (PfRule r # ls) \<gamma> p (Preliminary x2)) =
                             unwrap_decision (filter_approx ls \<gamma> p (Preliminary x2))"
              using TernaryUnknown by (simp add:matches_def)
            obtain d' where *:"filter_approx (remove_quick_approx ls) \<gamma> p (Preliminary x2) = 
                             (Preliminary d')" using prem is_Preliminary_def by blast
            then have "filter_approx ((remove_quick_approx ls)@[PfRule (r\<lparr>get_quick := False\<rparr>)]) \<gamma> p (Preliminary x2) =
                       filter_approx [PfRule (r\<lparr>get_quick := False\<rparr>)] \<gamma> p (Preliminary d')"
              by(simp add:filter_approx_chain)
            moreover have "\<not>(snd \<gamma>) (pf_rule.get_action r) d' p"
              using False 2(4) 2(5) unfolding good_matcher_def apply(auto split:action.splits) by metis
            ultimately have "(filter_approx (remove_quick_approx (PfRule r # ls)) \<gamma> p (Preliminary x2)) = (Preliminary d')" (is "?dw = (Preliminary ?d)")
              using TernaryUnknown quick by (simp add:matches_def)
            then have res2:"unwrap_decision ?dw = ?d" by auto
            have a:"unwrap_decision (filter_approx (remove_quick_approx ls) \<gamma> p (Preliminary x2)) = d'" using * by simp
            then have "unwrap_decision (filter_approx ls \<gamma> p (Preliminary x2)) = d'" using a 2 by auto
            then have "unwrap_decision (filter_approx (PfRule r # ls) \<gamma> p (Preliminary x2)) = d'" using res1 TernaryUnknown False quick by simp
            then show ?thesis using Preliminary res2 by simp
          qed
        qed
      next
        case False
        then show ?thesis using 2 Preliminary by auto
      qed
    qed
  next
  case (3 vb vc va)
    then show ?case by auto
  qed
  then show ?thesis by (simp add:pf_approx_def)
qed

(* remove matches *)

fun remove_matches :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_matches [] = []"
|"remove_matches ((PfRule r)#ls) =
(if ((pf_rule.get_action r) = ActionMatch)
  then remove_matches ls
  else (PfRule r)#remove_matches ls)"
|"remove_matches (l#ls) = l#(remove_matches ls)"

lemma remove_matches_preserves_filter_semantics:
  assumes "no_match_quick rs"
      and "no_anchors rs"
    shows "filter_approx rs \<gamma> p (Preliminary d) =
           filter_approx (remove_matches rs) \<gamma> p (Preliminary d)"
  using assms
  by (induction rs arbitrary:d rule: remove_matches.induct; (simp add:no_match_quick_def))

lemma remove_matches_preserves_semantics:
  assumes "no_match_quick rs"
      and "no_anchors rs"
    shows "pf_approx rs \<gamma> p = pf_approx (remove_matches rs) \<gamma> p"
  using assms unfolding pf_approx_def by (simp add:remove_matches_preserves_filter_semantics)

lemma remove_matches_ok:
  assumes "no_match_quick rs"
      and "no_anchors rs"
    shows "no_match (remove_matches rs)"
  using assms by (induction rs rule: remove_matches.induct) (simp add:no_match_quick_def)+

lemma remove_matches_preserves_no_anchors:
  assumes "no_anchors rs"
    shows "no_anchors (remove_matches rs)"
  using assms by (induction rs rule: remove_matches.induct) simp+

(* to_simple_ruleset *)

definition to_simple_ruleset :: "'a line list \<Rightarrow> 'a line list" where
"to_simple_ruleset rs = remove_quick_approx (remove_matches (remove_anchors' rs))"

lemma to_simple_ruleset:
  assumes "no_match_quick rs"
      and "no_unknown_anchors (common_matcher ctx, pfprefix_Unknown_Match_Tacs.in_doubt_allow) rs"
  shows
 "pf_approx rs (common_matcher ctx, in_doubt_allow) p =
  pf_approx (to_simple_ruleset rs) (common_matcher ctx, in_doubt_allow) p"
  and "simple_ruleset (to_simple_ruleset rs)"
proof(-)
  have *: "(pf_approx rs (common_matcher ctx, in_doubt_allow) p) =
        (pf_approx (remove_anchors' rs) (common_matcher ctx, in_doubt_allow) p)"
    (is "?original = pf_approx (?anchors_removed) ?m ?p")
    using assms by (simp add:remove_anchors'_preserves_semantics)
  have na:"no_anchors ?anchors_removed"
    by (simp add:remove_anchors'_ok)
  have nmq:"no_match_quick ?anchors_removed"
    using assms remove_anchors'_preserves_no_match_quick by blast
  have *: "?original = pf_approx (remove_matches ?anchors_removed) ?m ?p"
(is "?original = pf_approx (?matches_removed) ?m ?p")
    using * na nmq assms by(auto simp add:remove_matches_preserves_semantics)
  have nm:"no_match ?matches_removed"
    using na nmq remove_matches_ok by blast
  have na:"no_anchors ?matches_removed"
    using na using remove_matches_preserves_no_anchors by blast
  have gm:"good_matcher ?m"
    by (simp add:in_doubt_allow_good_matcher)
  have *: "?original = pf_approx (remove_quick_approx ?matches_removed) ?m ?p"
    (is "?original = pf_approx (?quick_removed) ?m ?p")
    using * na nm gm assms by(simp add:remove_quick_approx_preserves_semantics)
  then show "pf_approx rs (common_matcher ctx, in_doubt_allow) p =
  pf_approx (to_simple_ruleset rs) (common_matcher ctx, in_doubt_allow) p" 
    unfolding to_simple_ruleset_def by simp
  have nq:"no_quick ?quick_removed"
    using na remove_quick_approx_ok by blast
  have nm:"no_match ?quick_removed"
    using na nm remove_quick_approx_preserves_no_match by blast
  have na:"no_anchors ?quick_removed"
    using na remove_quick_approx_preserves_no_anchors by blast
  from nq nm na show "simple_ruleset (to_simple_ruleset rs)"
    unfolding to_simple_ruleset_def by (simp add:simple_ruleset_def)
qed

(* simple ruleset reverse *)

fun match_pf_rule :: "'a line \<Rightarrow> ('a,'p) match_tac \<Rightarrow> 'p \<Rightarrow> bool" where
(* Accept is arbitrary here, \<gamma> should be independent of d *)
"match_pf_rule (PfRule r) \<gamma> p = matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) decision.Accept p"

lemma rev_preserves_no_match[simp]:
  assumes "no_match rules"
  shows "no_match (rev rules)"
  using assms by (induction rules) auto

lemma rev_preserves_no_quick[simp]:
  assumes "no_quick rules"
  shows "no_quick (rev rules)"
  using assms by (induction rules) auto

lemma rev_preserves_no_anchors[simp]:
  assumes "no_anchors rules"
  shows "no_anchors (rev rules)"
  using assms by (induction rules) auto

lemma good_matcher_match:
  assumes "good_matcher \<gamma>"
      and "matches \<gamma> m a d p"
      and "a \<noteq> ActionMatch"
    shows "\<And>d. matches \<gamma> m a d p"
  using assms
  apply(cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m))")
    apply (auto simp:matches_def good_matcher_def) by metis

lemma good_matcher_match_not:
  assumes "good_matcher \<gamma>"
      and "\<not>matches \<gamma> m a d p"
      and "a \<noteq> ActionMatch"
    shows "\<And>d. \<not>matches \<gamma> m a d p"
  using assms
  apply(cases "(ternary_ternary_eval (map_match_tac (fst \<gamma>) p m))")
  apply (auto simp:matches_def good_matcher_def) by metis

lemma pf_reverse_semantics:
  assumes "simple_rset rs"
      and "good_matcher \<gamma>"
    shows "pf_approx (rev rs) \<gamma> p = (case (find (\<lambda>r. match_pf_rule r \<gamma> p) rs) of
(Some (PfRule r)) \<Rightarrow> (action_to_decision (pf_rule.get_action r) decision.Accept)
| None \<Rightarrow> decision.Accept)"
    using assms unfolding pf_approx_def simple_rset_def
proof(induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case
  proof(cases a)
    case (PfRule r)
    then show ?thesis
    proof(cases "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) decision.Accept p")
      have "is_Preliminary (filter_approx (rev rs) \<gamma> p (Preliminary decision.Accept))" using Cons by (simp add:no_quick_preliminary[of "(rev rs)"])
      then obtain d where *:"(filter_approx (rev rs) \<gamma> p (Preliminary decision.Accept)) = (Preliminary d)"
        using is_Preliminary_def by blast
      case True
      then have "matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) d p"
        using Cons PfRule by(auto simp:good_matcher_match)
      then have "(filter_approx (rev rs @ [PfRule r]) \<gamma> p (Preliminary decision.Accept)) =
                        Preliminary (action_to_decision (pf_rule.get_action r) d)"
        using Cons PfRule * by (simp add:filter_approx_chain)
      then show ?thesis using Cons PfRule True by (cases "pf_rule.get_action r") auto
    next
      case False
      then have "\<not>matches \<gamma> (pf_rule.get_match r) (pf_rule.get_action r) (unwrap_decision (filter_approx (rev rs) \<gamma> p (Preliminary decision.Accept))) p"
        using Cons PfRule by(auto simp:good_matcher_match_not)
      then have "filter_approx (rev rs @ [PfRule r]) \<gamma> p (Preliminary decision.Accept) =
                  filter_approx (rev rs) \<gamma> p (Preliminary decision.Accept)" by simp
      then show ?thesis using Cons PfRule False by auto
    qed
  next
    case (Anchor x21 x22)
    then show ?thesis using Cons by auto
  qed
qed

end