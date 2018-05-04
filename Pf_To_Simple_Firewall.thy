theory Pf_To_Simple_Firewall
imports PF
        Simple_Firewall.SimpleFw_Semantics
begin

fun and_each :: "anchor_rule \<Rightarrow> line list \<Rightarrow> line list" where
"and_each _ [] = []"|
"and_each r (l#ls) = (and l r)#(and_each r ls)"

fun remove_anchors :: "line list \<Rightarrow> line list" where
"remove_anchors [] = []"|
"remove_anchors ((Anchor rule lines) # rs) = (and_each rule lines) @ (remove_anchors rs)"|
"remove_anchors (r#rs) = r#(remove_anchors rs)"

lemma remove_anchors_preserves_semantics : "\<forall> rules : pf rules = pf (remove_anchors rules)"

remove_quick :: "line list \<Rightarrow> line list" where
"remove_quick [] = []"|
"remove_quick (r#rs) = (set_quick_false r)#(remove_quick (if (quick? r) then (and_each (not r) rs) else rs))"

lemma remove_quick_preserves_semantics : "\<forall> rules : pf rules = pf (remove_quick rules)"

fun pf_to_simplefw :: "line list \<Rightarrow> simple_match list" where
"pf_to_simplefw rules = (map to_simple_match (reverse (normalize (remove_quick (remove_anchors rules)))))"

end