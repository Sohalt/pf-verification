theory Matching
imports Main
begin
(* Taken from Iptaples_Semantics*)
datatype 'a match_expr = Match 'a
                       | MatchNot "'a match_expr"
                       | MatchAnd "'a match_expr" "'a match_expr"
                       | MatchAny

definition MatchOr :: "'a match_expr \<Rightarrow> 'a match_expr \<Rightarrow> 'a match_expr" where
  "MatchOr m1 m2 = MatchNot (MatchAnd (MatchNot m1) (MatchNot m2))"


text\<open>A matcher (parameterized by the type of primitive @{typ 'a} and packet @{typ 'p})
     is a function which just tells whether a given primitive and packet matches.\<close>
type_synonym ('a, 'p) matcher = "'a \<Rightarrow> 'p \<Rightarrow> bool"


text\<open>Given an @{typ "('a, 'p) matcher"} and a match expression, does a packet of type @{typ 'p}
     match the match expression?\<close>
fun matches :: "('a, 'p) matcher \<Rightarrow> 'a match_expr \<Rightarrow> 'p \<Rightarrow> bool" where
"matches \<gamma> (MatchAnd e1 e2) p \<longleftrightarrow> matches \<gamma> e1 p \<and> matches \<gamma> e2 p" |
"matches \<gamma> (MatchNot me) p \<longleftrightarrow> \<not> matches \<gamma> me p" |
"matches \<gamma> (Match e) p \<longleftrightarrow> \<gamma> e p" |
"matches _ MatchAny _ \<longleftrightarrow> True"
(* end *)
end