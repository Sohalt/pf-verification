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

(* lemma remove_anchors_preserves_semantics : "\<forall> rules : pf rules = pf (remove_anchors rules)" *)

remove_quick :: "line list \<Rightarrow> line list" where
"remove_quick [] = []"|
"remove_quick (r#rs) = (set_quick_false r)#(remove_quick (if (quick? r) then (and_each (not r) rs) else rs))"

lemma remove_quick_preserves_semantics : "\<forall> rules : pf rules = pf (remove_quick rules)"

fun pf_to_simplefw :: "line list \<Rightarrow> simple_match list" where
"pf_to_simplefw rules = (map to_simple_match (reverse (normalize (remove_quick (remove_anchors rules)))))"

end