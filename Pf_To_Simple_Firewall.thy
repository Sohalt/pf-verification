theory Pf_To_Simple_Firewall
imports PF
        Simple_Firewall.SimpleFw_Semantics
begin

fun and_line :: "'a match_expr \<Rightarrow> 'a line \<Rightarrow> 'a line" where
"and_line m Option =Option"|
"and_line m (PfRule r) = (PfRule (r\<lparr>pf_rule2.get_match := (MatchAnd m (pf_rule2.get_match r))\<rparr>))"|
"and_line m (Anchor r l) = (Anchor (r\<lparr>anchor_rule2.get_match := (MatchAnd m (anchor_rule2.get_match r))\<rparr>) l)"

fun and_each :: "'a match_expr \<Rightarrow> 'a ruleset \<Rightarrow> 'a ruleset" where
"and_each _ [] = []"|
"and_each m (l#ls) = (and_line m l)#(and_each m ls)"

fun remove_anchors :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_anchors [] = []"|
"remove_anchors ((Anchor r l) # rs) = (and_each (anchor_rule2.get_match r) l) @ (remove_anchors rs)"|
"remove_anchors (r#rs) = r#(remove_anchors rs)"


fun is_quick_rule :: "'a line \<Rightarrow> bool" where
"is_quick_rule (PfRule r) = (get_quick r)"
| "is_quick_rule _ = False"

lemma pf_add_common_prefix : "pf l1 m p = pf l2 m p \<Longrightarrow> pf (l#l1) m p = pf (l#l2) m p"
  show "(pf l1 m p = pf l2 m p)" is "?premise"
proof (cases l)
  case Option
  then 
  show "l = Option \<Longrightarrow> pf l1 m p = pf l2 m p \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p" by auto
next
  show "l = PfRule r \<Longrightarrow> pf l1 m p = pf l2 m p \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p"
  proof(cases (matches m (pf_rule2.get_match r p)))
  case (PfRule r)
  have "\<not> (matches m (pf_rule2.get_match r) p) \<Longrightarrow> pf l1 m p = pf l2 m p \<Longrightarrow>
          l = (PfRule r) \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p" by simp
  assume Matches:"(matches m (pf_rule2.get_match r) p)"
  moreover assume "(pf_rule2.get_quick r)"
  then have "(matches m (pf_rule2.get_match r) p) \<and> (pf_rule2.get_quick r) \<Longrightarrow> pf l1 m p = pf l2 m p \<Longrightarrow>
          l = (PfRule r) \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p" by simp
  assume "\<not>(pf_rule2.get_quick r)"
  then have "(matches m (pf_rule2.get_match r) p) \<and> \<not>(pf_rule2.get_quick r) \<Longrightarrow> pf l1 m p = pf l2 m p \<Longrightarrow>
          l = (PfRule r) \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p"
    using \<open>get_quick r\<close> by blast
  then show "pf l1 m p = pf l2 m p \<Longrightarrow> l = PfRule x2 \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p" by sledgehammer
(*
  then show "l = PfRule r \<Longrightarrow>
          pf l1 m p = pf l2 m p \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p" by sorry
next
  case (Anchor a ls)
  then show "l = Anchor a ls \<Longrightarrow>
       pf l1 m p = pf l2 m p \<Longrightarrow> pf (l # l1) m p = pf (l # l2) m p" by sorry
qed
*)

definition ruleset_equiv :: "'a ruleset \<Rightarrow> 'a ruleset \<Rightarrow> bool" where
"ruleset_equiv l1 l2 = (\<forall> m p.(pf l1 m p = pf l2 m p))"

definition transform_preserves_semantics ::"('a ruleset \<Rightarrow> 'a ruleset) \<Rightarrow> bool" where
"transform_preserves_semantics transform \<equiv> \<forall> (rules \<in>'a ruleset). (ruleset_equiv rules (transform rules))"

lemma remove_anchors_preserves_semantics : "pf rules matcher packet = pf (remove_anchors rules) matcher packet"
(*lemma remove_anchors_preserves_semantics : "transform_preserves_semantics remove_anchors"*)
proof (induction rules)
  case Nil
  then show ?case by auto
next
  case (Cons a rules)
  then show ?case
  proof (cases a)
    case Option
    then show "pf rules matcher packet = pf (remove_anchors rules) matcher packet \<Longrightarrow> a = Option \<Longrightarrow> pf (a # rules) matcher packet = pf (remove_anchors (a # rules)) matcher packet" by auto
  next
    case (PfRule r)
    moreover assume IH:"pf rules matcher packet = pf (remove_anchors rules) matcher packet"
    from IH and pf_add_common_prefix have "pf (a#rules) matcher packet = pf (a#(remove_anchors rules)) matcher packet" by blast
    then show "pf rules matcher packet = pf (remove_anchors rules) matcher packet \<Longrightarrow>
          a = PfRule r \<Longrightarrow> pf (a # rules) matcher packet = pf (remove_anchors (a # rules)) matcher packet" by auto
  next
    case (Anchor m ls)
    moreover assume "matches matcher (get_match m) packet"

lemma and_each_preserves_length[simp] : "\<forall> mexp. length (and_each mexp rules) = length rules"
  by (induction rules, auto)

fun remove_quick :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick [] = []"|
"remove_quick ((PfRule r)#ls) = 
(if (get_quick r)
then
(remove_quick (and_each (MatchNot (pf_rule2.get_match r)) ls))@[PfRule (r\<lparr>get_quick := False\<rparr>)]
else
((PfRule r)#(remove_quick ls)))"|
"remove_quick (l#ls) = l#(remove_quick ls)"


fun remove_quick_alternate' :: "'a ruleset \<Rightarrow> 'a line list \<Rightarrow> 'a ruleset" where
"remove_quick_alternate' [] quick = quick"|
"remove_quick_alternate' ((PfRule r)#ls) quick = 
(if (get_quick r)
then remove_quick_alternate' ls (PfRule (r\<lparr>get_quick := False\<rparr>)#quick)
else (PfRule r)#(remove_quick_alternate' ls quick))"|
"remove_quick_alternate' (l#ls) quick = l#(remove_quick_alternate' ls quick)"

fun remove_quick_alternate :: "'a ruleset \<Rightarrow> 'a ruleset" where
"remove_quick_alternate rs = remove_quick_alternate' rs []"
(* remove_quick_alternate only works because we ignore any state altering rules.
If there would be rewriting/matching rules after the quick rule, that also match, they would take effect and might change the result.
With remove_quick, if something matches the quick rule, these rules explicitly cannot match, because they are ANDed with the negation of the quick rule's match condition.
TODO: check exact semantics of rewriting/matching rules (does only last rule or every matching rule get executed?)
*)

lemma remove_match_not:"matches matcher matchexp p \<longrightarrow> filter ((and_each (MatchNot matchexp) rules)@rules2) matcher p d = filter rules2 matcher p d"
  apply(induction rules)
   apply(auto)
  apply(case_tac a,simp,simp,simp)
  done

(*
lemma remove_quick_preserves_semantics : "pf rules matcher packet = pf (remove_quick rules) matcher packet"
  apply(induction rules)
   apply(auto)
  apply(case_tac a)
    apply(auto)
*)

lemma remove_quick_preserves_semantics : "pf rules matcher packet = pf (remove_quick rules) matcher packet"
proof (induction rules)
  show "pf [] matcher packet = pf (remove_quick []) matcher packet" by auto
next


(* induction on rules
case rule quick
true:
  case matches rule packet
    true:
      not matches rules packet
*)



(*
fun pf_to_simplefw :: "'a ruleset \<Rightarrow> 'a ruleset" where
"pf_to_simplefw rules = (map to_simple_match (reverse (normalize_firewall (remove_quick (remove_anchors rules)))))"
*)
end