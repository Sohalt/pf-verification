theory Tables
imports
  Primitives
  "HOL-Library.Simps_Case_Conv"
begin

definition valid_table :: "table \<Rightarrow> bool" where
"valid_table table \<longleftrightarrow> (\<forall> t \<in> set table . (case (ta t) of (IPv4 a) \<Rightarrow> valid_prefix a | (IPv6 a) \<Rightarrow> valid_prefix a))"

definition decision :: "table_entry \<Rightarrow> bool" where
"decision te = (\<not>is_Negated te)"

instantiation table_address :: linorder
begin
fun less_eq_table_address :: "table_address \<Rightarrow> table_address \<Rightarrow> bool" where
"less_eq_table_address (IPv4 a) (IPv4 b) = (a \<le> b)"
|"less_eq_table_address (IPv4 a) (IPv6 b) = True"
|"less_eq_table_address (IPv6 a) (IPv4 b) = False"
|"less_eq_table_address (IPv6 a) (IPv6 b) = (a \<le> b)"

case_of_simps less_eq_table_address_cases: less_eq_table_address.simps

fun less_table_address :: "table_address \<Rightarrow> table_address \<Rightarrow> bool" where
"less_table_address (IPv4 a) (IPv4 b) = (a < b)"
|"less_table_address (IPv4 a) (IPv6 b) = True"
|"less_table_address (IPv6 a) (IPv4 b) = False"
|"less_table_address (IPv6 a) (IPv6 b) = (a < b)"

case_of_simps less_table_address_cases: less_table_address.simps
thm less_table_address_cases

instance by standard (auto simp add: less_eq_table_address_cases less_table_address_cases split: table_address.splits)
end

instantiation table_entry :: linorder
begin
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


lemma find_Some_decision_addr_in_set:
  assumes "\<And>t. t \<in> set table \<Longrightarrow> isIPv4 (ta t)" "valid_table table"
  assumes "find (\<lambda>x. prefix_match_semantics (ip4 (ta x)) address) table = Some te"
  shows "decision te = (address \<in> table_to_set_v4 table)"
  using assms proof(induction table)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have vp: "valid_prefix (ip4 (ta x))" using Cons(2) Cons(3) unfolding valid_table_def
        by (auto simp add: table_address.case_eq_if)
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

lemma find_None_addr_not_in_set:
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
    using prefix_match_semantics_wordset Cons unfolding valid_table_def by (auto simp add: table_address.case_eq_if)
  ultimately show ?case using Cons unfolding valid_table_def
    by (simp add: table_entry.case_eq_if table_to_set_v4_def)
qed

lemma match_table_v4_inner:
  assumes "valid_table table" "\<And>t. t \<in> set table \<Longrightarrow> isIPv4 (ta t)"
  shows "match_table_v4_inner table address = match_table_v4'_inner table address"
  using assms
proof(cases "find (\<lambda>t. prefix_match_semantics (ip4 (ta t)) address) table")
  case None
  then show ?thesis unfolding match_table_v4_inner_def match_table_v4'_inner_def using find_None_addr_not_in_set assms by simp
next
  case (Some a)
  then show ?thesis unfolding match_table_v4_inner_def match_table_v4'_inner_def using find_Some_decision_addr_in_set assms by simp
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

(* IPv6 *)
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
    by (metis list.set_intros(1) table_address.case_eq_if table_address.distinct_disc(1))
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
    by (metis list.set_intros(1) table_address.case_eq_if table_address.distinct_disc(1))
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

(* table matching *)
fun lookup_table :: "string \<Rightarrow> table" where
"lookup_table _ = []" (* TODO *)

fun match_table :: "string \<Rightarrow> addr \<Rightarrow> bool" where
"match_table name (IPv4 addr) = match_table_v4 (lookup_table name) addr"
|"match_table name (IPv6 addr) = match_table_v6 (lookup_table name) addr"
end