theory Translation
imports
  Firewall_Common
  Primitives
  PrimitiveMatchers
  Intermediate_Representation
begin

(* normalize matches to representation closest to simple_matcher *)

fun match_or :: "'a list \<Rightarrow> 'a match_expr" where
"match_or [] = MatchNot MatchAny" |
"match_or (x#xs) = MatchOr (Match x) (match_or xs)"

(* words wrap \<rightarrow> needs explicit check for 0 and max_word *)
value "(WordInterval (max_word + 1) max_word)::16 wordinterval"

fun normalize_ports' :: "16 word opspec \<Rightarrow> 16 wordinterval" where
"normalize_ports' (Unary (Eq p)) = (WordInterval p p)" |
"normalize_ports' (Unary (NEq p)) = wordinterval_setminus wordinterval_UNIV (WordInterval p p)" |
"normalize_ports' (Unary (GtEq p)) = (WordInterval p max_word)" |
"normalize_ports' (Unary (Gt p)) = (if (p = max_word) then Empty_WordInterval else (WordInterval (p + 1) max_word))" |
"normalize_ports' (Unary (LtEq p)) = (WordInterval 0 p)" |
"normalize_ports' (Unary (Lt p)) = (if (p = 0) then Empty_WordInterval else (WordInterval 0 (p - 1)))" |
"normalize_ports' (Binary (RangeIncl from to)) = (WordInterval from to)" |
"normalize_ports' (Binary (RangeExcl from to)) = (if (from = max_word \<or> to = 0) then Empty_WordInterval else (WordInterval (from + 1) (to -1)))" |
"normalize_ports' (Binary (RangeComp from to)) = wordinterval_setminus wordinterval_UNIV (WordInterval from to)"

value "normalize_ports' (Binary (RangeComp 80 0))"

value "0 < (0::16 word)"

lemma normalize_ports :
"match_port spec p \<longleftrightarrow> wordinterval_element p (normalize_ports' spec)"
  unfolding match_port_def
proof(induction spec rule: normalize_ports'.induct)
case (1 p)
then show ?case by simp
next
  case (2 p)
  then show ?case by simp
next
case (3 p)
  then show ?case by simp
next
case (4 p)
  then show ?case apply (auto simp add: inc_le word_Suc_le)
    using linorder_not_less by blast
next
  case (5 p)
  then show ?case by simp
next
  case (6 p)
  then show ?case by (auto simp add: minus_one_helper3 minus_one_helper5)
next
  case (7 "from" to)
  then show ?case by simp
next
  case (8 "from" to)
  then show ?case apply (auto simp add: inc_le word_Suc_le minus_one_helper3 minus_one_helper5)
    using linorder_not_less by blast
next
  case (9 "from" to)
  then show ?case by auto
qed

end