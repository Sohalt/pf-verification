theory PF_Tables
imports
  PF_Primitives
  "HOL-Library.Simps_Case_Conv"
begin

definition decision :: "table_entry \<Rightarrow> bool" where
"decision te = (\<not>is_Negated te)"

instantiation address :: linorder
begin
fun less_eq_address :: "address \<Rightarrow> address \<Rightarrow> bool" where
"less_eq_address (IPv4 a) (IPv4 b) = (a \<le> b)"
|"less_eq_address (IPv4 a) (IPv6 b) = True"
|"less_eq_address (IPv6 a) (IPv4 b) = False"
|"less_eq_address (IPv6 a) (IPv6 b) = (a \<le> b)"

case_of_simps less_eq_address_cases: less_eq_address.simps

fun less_address :: "address \<Rightarrow> address \<Rightarrow> bool" where
"less_address (IPv4 a) (IPv4 b) = (a < b)"
|"less_address (IPv4 a) (IPv6 b) = True"
|"less_address (IPv6 a) (IPv4 b) = False"
|"less_address (IPv6 a) (IPv6 b) = (a < b)"

case_of_simps less_address_cases: less_address.simps
thm less_address_cases

instance by standard (auto simp add: less_eq_address_cases less_address_cases split: address.splits)
end

instantiation table_entry :: linorder
begin
(* depends on correct order of prefix_match *)
fun less_eq_table_entry :: "table_entry \<Rightarrow> table_entry \<Rightarrow> bool" where
"less_eq_table_entry (TableEntry a) (TableEntry b) = (a \<le> b)"
|"less_eq_table_entry (TableEntry a) (TableEntryNegated b) = True"
|"less_eq_table_entry (TableEntryNegated a) (TableEntry b) = False"
|"less_eq_table_entry (TableEntryNegated a) (TableEntryNegated b) = (a \<le> b)"

case_of_simps less_eq_table_entry_cases: less_eq_table_entry.simps

fun less_table_entry :: "table_entry \<Rightarrow> table_entry \<Rightarrow> bool" where
"less_table_entry (TableEntry a) (TableEntry b) = (a < b)"
|"less_table_entry (TableEntry a) (TableEntryNegated b) = True"
|"less_table_entry (TableEntryNegated a) (TableEntry b) = False"
|"less_table_entry (TableEntryNegated a) (TableEntryNegated b) = (a < b)"

case_of_simps less_table_entry_cases: less_table_entry.simps
thm less_table_entry_cases

instance by standard (auto simp add: less_eq_table_entry_cases less_table_entry_cases split: table_entry.splits)
end


(* IPv4 *)

definition match_table_v4_inner :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4_inner table addr =
 (case (find (\<lambda> t . prefix_match_semantics (ip4 (ta t)) addr) table) of
 (Some t) \<Rightarrow> decision t |None \<Rightarrow> False)"

definition match_table_v4 :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4 table addr = match_table_v4_inner (sort [t \<leftarrow> table. isIPv4 (ta t)]) addr"


abbreviation foldf_v4 :: "table_entry \<Rightarrow> 32 word set \<Rightarrow> 32 word set" where
"foldf_v4 t a \<equiv> (case t of (TableEntry te) \<Rightarrow> a \<union> prefix_to_wordset (ip4 te) | (TableEntryNegated te) \<Rightarrow> a - prefix_to_wordset  (ip4 te))"

definition table_to_set_v4 :: "table \<Rightarrow> 32 word set" where
"table_to_set_v4 table = foldr foldf_v4 table {}"

definition match_table_v4'_inner :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4'_inner table address \<longleftrightarrow> address \<in> table_to_set_v4 table"

definition match_table_v4' :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4' table address = match_table_v4'_inner (sort [t \<leftarrow> table. isIPv4 (ta t)]) address"


abbreviation foldf_wi_v4 :: "table_entry \<Rightarrow> 32 wordinterval \<Rightarrow> 32 wordinterval" where
"foldf_wi_v4 t a \<equiv> (case t of (TableEntry te) \<Rightarrow> wordinterval_union a (prefix_to_wordinterval (ip4 te))
 | (TableEntryNegated te) \<Rightarrow> wordinterval_setminus a (prefix_to_wordinterval (ip4 te)))"

definition table_to_wordinterval_v4_inner :: "table \<Rightarrow> 32 wordinterval" where
"table_to_wordinterval_v4_inner table = foldr foldf_wi_v4 table Empty_WordInterval"

definition table_to_wordinterval_v4 :: "table \<Rightarrow> 32 wordinterval" where
"table_to_wordinterval_v4 table = table_to_wordinterval_v4_inner (sort [t \<leftarrow> table. isIPv4 (ta t)])"


lemma table_to_wordinterval_v4: "wordinterval_to_set (table_to_wordinterval_v4_inner table) = table_to_set_v4 table"
  unfolding table_to_set_v4_def table_to_wordinterval_v4_inner_def
  by (induction table ) (auto split:table_entry.splits)


lemma match_table_v4': "match_table_v4' table addr = wordinterval_element addr (table_to_wordinterval_v4 table)"
  unfolding match_table_v4'_def table_to_wordinterval_v4_def match_table_v4'_inner_def using table_to_wordinterval_v4 by auto


lemma find_Some_decision_addr_in_set_v4:
  assumes "\<And>t. t \<in> set table \<Longrightarrow> isIPv4 (ta t)" "valid_table table"
  assumes "find (\<lambda>x. prefix_match_semantics (ip4 (ta x)) address) table = Some te"
  shows "decision te = (address \<in> table_to_set_v4 table)"
  using assms proof(induction table)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have vp: "valid_prefix (ip4 (ta x))" using Cons(2) Cons(3) unfolding valid_table_def
        by (auto simp add: address.case_eq_if)
  show ?case
  proof(cases "prefix_match_semantics (ip4 (ta x)) address")
    case True
    then have *:"find (\<lambda>x. prefix_match_semantics (ip4 (ta x)) address) (x # xs) = Some x" by auto
    have **:"address \<in> prefix_to_wordset (ip4 (ta x))" using vp True prefix_match_semantics_wordset unfolding valid_table_def by auto
    then show ?thesis
    proof(cases x)
      case (TableEntry x1)
      then show ?thesis unfolding table_to_set_v4_def decision_def using Cons * ** by auto
    next
      case (TableEntryNegated x2)
      then show ?thesis unfolding table_to_set_v4_def decision_def using Cons * ** by auto
    qed
  next
    case False
    then have *: "find (\<lambda>x. prefix_match_semantics (ip4 (ta x)) address) xs = Some te" using Cons by auto
    have vt: "valid_table xs" using Cons(3) by (simp add:valid_table_def)
      then show ?thesis
      proof(cases x)
        case (TableEntry x1)
        then have "decision te = (address \<in> table_to_set_v4 xs)" using * vt Cons by auto
        then show ?thesis unfolding table_to_set_v4_def using False vp prefix_match_semantics_wordset TableEntry by auto
      next
        case (TableEntryNegated x2)
        then have "decision te = (address \<in> table_to_set_v4 xs)" using * vt Cons by auto
        then show ?thesis unfolding table_to_set_v4_def using False vp prefix_match_semantics_wordset TableEntryNegated by auto
      qed
  qed
qed

lemma find_None_addr_not_in_set_v4:
  assumes "\<And>t. t \<in> set table \<Longrightarrow> isIPv4 (ta t)" "valid_table table"
  assumes "find (\<lambda>x. prefix_match_semantics (ip4 (ta x)) address) table = None"
  shows "address \<notin> table_to_set_v4 table"
  using assms
proof(induction table)
  case Nil
  then show ?case unfolding table_to_set_v4_def by simp
next
  case (Cons a table)
  then have *:"\<not>prefix_match_semantics (ip4 (ta a)) address" by auto
  moreover have "prefix_match_semantics (ip4 (ta a)) address = (address \<in> prefix_to_wordset (ip4 (ta a)))"
    using prefix_match_semantics_wordset Cons unfolding valid_table_def by (auto simp add: address.case_eq_if)
  ultimately show ?case using Cons unfolding valid_table_def
    by (simp add: table_entry.case_eq_if table_to_set_v4_def)
qed

lemma match_table_v4_inner:
  assumes "valid_table table" "\<And>t. t \<in> set table \<Longrightarrow> isIPv4 (ta t)"
  shows "match_table_v4_inner table address = match_table_v4'_inner table address"
  using assms
proof(cases "find (\<lambda>t. prefix_match_semantics (ip4 (ta t)) address) table")
  case None
  then show ?thesis unfolding match_table_v4_inner_def match_table_v4'_inner_def using find_None_addr_not_in_set_v4 assms by simp
next
  case (Some a)
  then show ?thesis unfolding match_table_v4_inner_def match_table_v4'_inner_def using find_Some_decision_addr_in_set_v4 assms by simp
qed

lemma match_table_v4:
  assumes "valid_table table"
  shows "match_table_v4 table address = match_table_v4' table address"
  using assms
proof(-)
  have "\<And>t. t \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]) \<Longrightarrow> isIPv4 (ta t)" by auto
  moreover have "valid_table (sort [t\<leftarrow>table . isIPv4 (ta t)])" using assms by (simp add: valid_table_def)
  ultimately show ?thesis unfolding match_table_v4_def match_table_v4'_def using match_table_v4_inner
    by blast
qed


lemma match_table_v4_wordinterval:
  assumes "valid_table table"
  shows "match_table_v4 table address = wordinterval_element address (table_to_wordinterval_v4 table)"
  using assms match_table_v4 match_table_v4' by simp


(* IPv6 *) (* largely copied from above *)

definition match_table_v6_inner :: "table \<Rightarrow> 128 word \<Rightarrow> bool" where
"match_table_v6_inner table addr =
 (case (find (\<lambda> t . prefix_match_semantics (ip6 (ta t)) addr) table) of
 (Some t) \<Rightarrow> decision t |None \<Rightarrow> False)"

definition match_table_v6 :: "table \<Rightarrow> 128 word \<Rightarrow> bool" where
"match_table_v6 table addr = match_table_v6_inner (sort [t \<leftarrow> table. isIPv6 (ta t)]) addr"


abbreviation foldf_v6 :: "table_entry \<Rightarrow> 128 word set \<Rightarrow> 128 word set" where
"foldf_v6 t a \<equiv> (case t of (TableEntry te) \<Rightarrow> a \<union> prefix_to_wordset (ip6 te) | (TableEntryNegated te) \<Rightarrow> a - prefix_to_wordset  (ip6 te))"

definition table_to_set_v6 :: "table \<Rightarrow> 128 word set" where
"table_to_set_v6 table = foldr foldf_v6 table {}"

definition match_table_v6'_inner :: "table \<Rightarrow> 128 word \<Rightarrow> bool" where
"match_table_v6'_inner table address \<longleftrightarrow> address \<in> table_to_set_v6 table"

definition match_table_v6' :: "table \<Rightarrow> 128 word \<Rightarrow> bool" where
"match_table_v6' table address = match_table_v6'_inner (sort [t \<leftarrow> table. isIPv6 (ta t)]) address"


abbreviation foldf_wi_v6 :: "table_entry \<Rightarrow> 128 wordinterval \<Rightarrow> 128 wordinterval" where
"foldf_wi_v6 t a \<equiv> (case t of (TableEntry te) \<Rightarrow> wordinterval_union a (prefix_to_wordinterval (ip6 te))
 | (TableEntryNegated te) \<Rightarrow> wordinterval_setminus a (prefix_to_wordinterval (ip6 te)))"

definition table_to_wordinterval_v6_inner :: "table \<Rightarrow> 128 wordinterval" where
"table_to_wordinterval_v6_inner table = foldr foldf_wi_v6 table Empty_WordInterval"

definition table_to_wordinterval_v6 :: "table \<Rightarrow> 128 wordinterval" where
"table_to_wordinterval_v6 table = table_to_wordinterval_v6_inner (sort [t \<leftarrow> table. isIPv6 (ta t)])"


lemma table_to_wordinterval_v6: "wordinterval_to_set (table_to_wordinterval_v6_inner table) = table_to_set_v6 table"
  unfolding table_to_set_v6_def table_to_wordinterval_v6_inner_def
  by (induction table ) (auto split:table_entry.splits)


lemma match_table_v6': "match_table_v6' table addr = wordinterval_element addr (table_to_wordinterval_v6 table)"
  unfolding match_table_v6'_def table_to_wordinterval_v6_def match_table_v6'_inner_def using table_to_wordinterval_v6 by auto


lemma find_Some_decision_addr_in_set_v6:
  assumes "\<And>t. t \<in> set table \<Longrightarrow> isIPv6 (ta t)" "valid_table table"
  assumes "find (\<lambda>x. prefix_match_semantics (ip6 (ta x)) address) table = Some te"
  shows "decision te = (address \<in> table_to_set_v6 table)"
  using assms proof(induction table)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have vp: "valid_prefix (ip6 (ta x))" using Cons(2) Cons(3) unfolding valid_table_def
    by (metis address.collapse(2) address.simps(6) list.set_intros(1))
  show ?case
  proof(cases "prefix_match_semantics (ip6 (ta x)) address")
    case True
    then have *:"find (\<lambda>x. prefix_match_semantics (ip6 (ta x)) address) (x # xs) = Some x" by auto
    have **:"address \<in> prefix_to_wordset (ip6 (ta x))" using vp True prefix_match_semantics_wordset unfolding valid_table_def by auto
    then show ?thesis
    proof(cases x)
      case (TableEntry x1)
      then show ?thesis unfolding table_to_set_v6_def decision_def using Cons * ** by auto
    next
      case (TableEntryNegated x2)
      then show ?thesis unfolding table_to_set_v6_def decision_def using Cons * ** by auto
    qed
  next
    case False
    then have *: "find (\<lambda>x. prefix_match_semantics (ip6 (ta x)) address) xs = Some te" using Cons by auto
    have vt: "valid_table xs" using Cons(3) by (simp add:valid_table_def)
      then show ?thesis
      proof(cases x)
        case (TableEntry x1)
        then have "decision te = (address \<in> table_to_set_v6 xs)" using * vt Cons by auto
        then show ?thesis unfolding table_to_set_v6_def using False vp prefix_match_semantics_wordset TableEntry by auto
      next
        case (TableEntryNegated x2)
        then have "decision te = (address \<in> table_to_set_v6 xs)" using * vt Cons by auto
        then show ?thesis unfolding table_to_set_v6_def using False vp prefix_match_semantics_wordset TableEntryNegated by auto
      qed
  qed
qed

lemma find_None_addr_not_in_set_v6:
  assumes "\<And>t. t \<in> set table \<Longrightarrow> isIPv6 (ta t)" "valid_table table"
  assumes "find (\<lambda>x. prefix_match_semantics (ip6 (ta x)) address) table = None"
  shows "address \<notin> table_to_set_v6 table"
  using assms
proof(induction table)
  case Nil
  then show ?case unfolding table_to_set_v6_def by simp
next
  case (Cons a table)
  then have *:"\<not>prefix_match_semantics (ip6 (ta a)) address" by auto
  moreover have "prefix_match_semantics (ip6 (ta a)) address = (address \<in> prefix_to_wordset (ip6 (ta a)))"
    using prefix_match_semantics_wordset Cons unfolding valid_table_def
    by (metis address.case_eq_if address.distinct_disc(1) list.set_intros(1))
  ultimately show ?case using Cons unfolding valid_table_def
    by (simp add: table_entry.case_eq_if table_to_set_v6_def)
qed

lemma match_table_v6_inner:
  assumes "valid_table table" "\<And>t. t \<in> set table \<Longrightarrow> isIPv6 (ta t)"
  shows "match_table_v6_inner table address = match_table_v6'_inner table address"
  using assms
proof(cases "find (\<lambda>t. prefix_match_semantics (ip6 (ta t)) address) table")
  case None
  then show ?thesis unfolding match_table_v6_inner_def match_table_v6'_inner_def using find_None_addr_not_in_set_v6 assms by simp
next
  case (Some a)
  then show ?thesis unfolding match_table_v6_inner_def match_table_v6'_inner_def using find_Some_decision_addr_in_set_v6 assms by simp
qed

lemma match_table_v6:
  assumes "valid_table table"
  shows "match_table_v6 table address = match_table_v6' table address"
  using assms
proof(-)
  have "\<And>t. t \<in> set (sort [t\<leftarrow>table . isIPv6 (ta t)]) \<Longrightarrow> isIPv6 (ta t)" by auto
  moreover have "valid_table (sort [t\<leftarrow>table . isIPv6 (ta t)])" using assms by (simp add: valid_table_def)
  ultimately show ?thesis unfolding match_table_v6_def match_table_v6'_def using match_table_v6_inner
    by blast
qed


lemma match_table_v6_wordinterval:
  assumes "valid_table table"
  shows "match_table_v6 table address = wordinterval_element address (table_to_wordinterval_v6 table)"
  using assms match_table_v6 match_table_v6' by simp
end