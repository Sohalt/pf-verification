theory PrimitiveMatchers
  imports Primitives
          Simple_Firewall.Simple_Packet
          Matching
          "HOL-Library.Simps_Case_Conv"
begin
fun match_interface :: "direction option \<Rightarrow> iface option \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_interface (Some In) (Some iface) p = ((p_iiface p) = iface)" |
"match_interface (Some In) None p = ((p_iiface p) \<noteq> [])" |
"match_interface (Some Out) (Some iface) p = ((p_oiface p) = iface)" |
"match_interface (Some Out) None p = ((p_oiface p) \<noteq> [])" |
"match_interface None (Some iface) p = ((p_iiface p = iface) \<or> (p_oiface p = iface))" |
"match_interface None None p = True"

fun match_iiface :: "iface \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_iiface iface p \<longleftrightarrow> (p_iiface p) = iface"

fun match_oiface :: "iface \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_oiface iface p \<longleftrightarrow> (p_oiface p) = iface"

fun match_af:: "afspec \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_af Inet _ = True" |
"match_af Inet6 _ = False" (* TODO ipv6 *)

(* uses protocol from Simple_Firewall.L4_Protocol, pf doesn't have "ProtoAny" (no protocol specified means "ProtoAny") *)
fun match_proto:: "primitive_protocol list \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_proto [] _ = False"|
"match_proto (p#ps) pkt = ((p_proto pkt = p) \<or> match_proto ps pkt)"

fun match_address :: "address \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_address _ _ = True" -- TODO

fun lookup_table :: "string \<Rightarrow> table" where
"lookup_table _ = []" (* TODO *)

fun decision :: "table_entry \<Rightarrow> bool" where
"decision (TableEntry _) = True"
|"decision (TableEntryNegated _) = False"

case_of_simps decision_cases: decision.simps

fun pfxm_length' :: "table_entry \<Rightarrow> nat" where
"pfxm_length' (TableEntry t) = (case t of (IPv4 a) \<Rightarrow> pfxm_length a | (IPv6 a) \<Rightarrow> pfxm_length a)"
|"pfxm_length' (TableEntryNegated t) = (case t of (IPv4 a) \<Rightarrow> pfxm_length a | (IPv6 a) \<Rightarrow> pfxm_length a)"

fun matches_v4 :: "table_entry \<Rightarrow> 32 word \<Rightarrow> bool" where
"matches_v4 t addr = (case (case t of (TableEntry t) \<Rightarrow> t | (TableEntryNegated t) \<Rightarrow> t) of (IPv4 a) \<Rightarrow> prefix_match_semantics a addr | (IPv6 a) \<Rightarrow> False)"

fun match_table'_v4 :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table'_v4 table addr =
 fst (fold (\<lambda> t (d,pfxml).
 if (matches_v4 t addr \<and> (pfxm_length' t > pfxml))
 then ((decision t),(pfxm_length' t))
 else (d,pfxml)) table (False,0::nat))"

fun match_table_v4 :: "string \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4 name ip = match_table'_v4 (lookup_table name) ip"


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


definition match_table_v4_alt :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4_alt table addr =
 (case (find (\<lambda> t . prefix_match_semantics (ip4 (ta t)) addr) table) of
 (Some t) \<Rightarrow> decision t |None \<Rightarrow> False)"

fun f :: "table_entry \<Rightarrow> 32 word set \<Rightarrow> 32 word set" where
"f t a = (case t of (TableEntry te) \<Rightarrow> a \<union> prefix_to_wordset (ip4 te) | (TableEntryNegated te) \<Rightarrow> a - prefix_to_wordset  (ip4 te))"

definition table_to_set_v4 :: "table \<Rightarrow> 32 word set" where
"table_to_set_v4 table = {word. match_table_v4_alt table word}"

lemma "table_to_set_v4 table = foldr f (sort (filter (\<lambda> t. isIPv4 (ta t)) table)) {}"
  sorry

definition match_table_v4_alt' :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4_alt' table address \<longleftrightarrow> address \<in> table_to_set_v4 table"

definition valid_table :: "table \<Rightarrow> bool" where
"valid_table table \<longleftrightarrow> (\<forall> t \<in> set table . (case (ta t) of (IPv4 a) \<Rightarrow> valid_prefix a | (IPv6 a) \<Rightarrow> valid_prefix a))"

lemma foo:
  assumes "\<exists> a. Min {x \<in> set l. P x} = a"
      and "sorted l"
    shows "\<exists> l1 l2. l = l1@a#l2 \<and> (\<forall> x \<in> (set l1). \<not>P x)"
  using assms
proof(-)
  have "{x \<in> set l. P x} \<subseteq> set l" by auto
  obtain a where "Min {x \<in> set l. P x} = a" using assms by blast
    then show ?thesis sorry
qed

lemma find_split:
  assumes "find P xs = Some x"
  shows "\<exists>xs1 xs2. xs = xs1 @ x # xs2 \<and> (\<forall>x \<in> set xs1. \<not> P x)"
using assms apply (induction xs) apply (auto split: if_splits)
apply fastforce
  sorry

lemma
  assumes "sorted table" "\<And>t. t \<in> set table \<Longrightarrow> isIPv4 (ta t)"
  assumes "find (\<lambda>x. prefix_match_semantics (ip4 (ta x)) address) table = Some (TableEntry te)"
  shows "address \<in> table_to_set_v4 table"
using assms proof (induction table rule: sorted.induct)
  case Nil
  then show ?case sorry
next
  case (Cons xs x)
  show ?case
    proof (cases "prefix_match_semantics (ip4 (ta x)) address")
      case True
      then show ?thesis
        unfolding table_to_set_v4_def match_table_v4_alt_def
        using Cons(5)
        by simp
    next
      case False
      then have "address \<in> table_to_set_v4 xs" sorry
      then show ?thesis
        unfolding table_to_set_v4_def match_table_v4_alt_def
        using False by auto
    qed
qed

lemma table_entry_matches_addr_in_set:
  assumes "\<exists> te . Min {x \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]). prefix_match_semantics (ip4 (ta x)) address} = TableEntry te"
  shows "address \<in> table_to_set_v4 table"
proof(-)
  obtain te where "Min {x \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]). prefix_match_semantics (ip4 (ta x)) address} = TableEntry te" using assms by blast
  then have "(sort [t\<leftarrow>table . isIPv4 (ta t)]) = t1@[TableEntry te]@t2" sorry
  then have "table_to_set_v4 table = foldr f (t1@[TableEntry te]) (foldr f t2 {})" by simp
  then have "table_to_set_v4 table = foldr f t1 ((foldr f t2 {}) \<union> prefix_to_wordset (ip4 te))" by simp
(* address not in range of any te in t1 \<rightarrow> even removing all of t1 (all TableEntryNegated) doesn't remove addr from foldr f t1 ((foldr f t2 {}) \<union> prefix_to_wordset (ip4 te)) *)
  then show ?thesis sorry
qed

lemma table_entry_negated_matches_addr_not_in_set:
  assumes "\<exists> te . Min {x \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]). prefix_match_semantics (ip4 (ta x)) address} = TableEntryNegated te"
  shows "address \<notin> table_to_set_v4 table"
proof(-)
  obtain te where "Min {x \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]). prefix_match_semantics (ip4 (ta x)) address} = TableEntryNegated te" using assms by blast
  then have "(sort [t\<leftarrow>table . isIPv4 (ta t)]) = t1@[TableEntryNegated te]@t2" sorry
  then have "table_to_set_v4 table = foldr f (t1@[TableEntryNegated te]) (foldr f t2 {})" by simp
  then have "table_to_set_v4 table = foldr f t1 ((foldr f t2 {}) - prefix_to_wordset (ip4 te))" by simp
(* address not in range of any te in t1 \<rightarrow> even adding all of t1 (all TableEntry) doesn't add addr to foldr f t1 ((foldr f t2 {}) - prefix_to_wordset (ip4 te)) *)
  show ?thesis sorry
qed

lemma match_table_v4:
  assumes "valid_table table"
  shows "match_table_v4_alt table address = match_table_v4_alt' table address"
  using assms
proof(cases "\<exists> x \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]) . prefix_match_semantics (ip4 (ta x)) address")
  case True
  then have *: "(find (\<lambda> t . prefix_match_semantics (ip4 (ta t)) address) (sort (filter (\<lambda> t. isIPv4 (ta t)) table))) =
 Some (Min {x \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]). prefix_match_semantics (ip4 (ta x)) address})"
    by (auto simp: sorted_find_Min)
  show ?thesis
  proof(cases "(Min {x \<in> set (sort [t\<leftarrow>table . isIPv4 (ta t)]). prefix_match_semantics (ip4 (ta x)) address})")
    case (TableEntry x1)
    then have **:"match_table_v4_alt table address = True" using * by simp
    have "match_table_v4_alt' table address = True" using TableEntry table_entry_matches_addr_in_set by (simp add:match_table_v4_alt'_def)
    then show ?thesis using ** by simp
  next
    case (TableEntryNegated x2)
    then have **:"match_table_v4_alt table address = False" using * by simp
    have "match_table_v4_alt' table address = False" using TableEntryNegated table_entry_negated_matches_addr_not_in_set by (simp add:match_table_v4_alt'_def)
    then show ?thesis using ** by simp
  qed
next
  case False
  then have "(find (\<lambda> t . prefix_match_semantics (ip4 (ta t)) address) (sort (filter (\<lambda> t. isIPv4 (ta t)) table))) = None" by (auto simp add: find_None_iff)
  then have *:"match_table_v4_alt table address = False" by auto
  have "match_table_v4_alt' table address = False" sorry
  then show ?thesis using * by simp
qed

(*

proof(cases "match_table_v4_alt table address")
  case True
  then have "\<exists> a. find (\<lambda>t. prefix_match_semantics (ip4 (ta t)) address) (sort [t\<leftarrow>table . isIPv4 (ta t)]) = Some (TableEntry (IPv4 a)) \<and> prefix_match_semantics a address" apply(auto simp: decision_cases split:table_entry.splits)
  then have "\<exists> a. (TableEntry (IPv4 a)) \<in> set table \<and> prefix_match_semantics a address" apply(simp)
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed


proof(induction "(sort (filter (\<lambda> t. isIPv4 (ta t)) table))")
  case Nil
  then show ?case by (simp add: match_table_v4_alt'_def)
next
  case IH: (Cons t tab)
  have "valid_table (t#tab)" using IH by (simp add:foo)
      then have vp: "valid_prefix (ip4 (ta t))"
        by (metis Cons_eq_filterD IH.hyps(2) filter_sort list.set_intros(1) table_address.case_eq_if valid_table_def)
    have *:"match_table_v4_alt table address =
 (case find (\<lambda>t. prefix_match_semantics (ip4 (ta t)) address) (t#tab) of None \<Rightarrow> False | Some x \<Rightarrow> decision x)"
      using IH by auto
    have **:"match_table_v4_alt' table address =
(address \<in>
 foldr (\<lambda>t a. case t of
 TableEntry te \<Rightarrow> a \<union> prefix_to_wordset (ip4 te)
 | TableEntryNegated te \<Rightarrow> a - prefix_to_wordset (ip4 te))
 (t#tab) {})"
      using IH by (auto simp:match_table_v4_alt'_def)
  then show ?case
  proof(cases "prefix_match_semantics (ip4 (ta t)) address")
    case True
    then show ?thesis using vp * ** by (auto simp add: prefix_match_semantics_wordset split:table_entry.splits)
  next
    case False
    then show ?thesis using vp * ** sorry
  qed
qed
*)

(* TODO ipv4 ipv6 versions
fun match_host :: "host \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_host (Address addr) ip = match_address addr ip"|
"match_host (NotAddress addr) ip = (\<not> (match_address addr ip))"|
"match_host (Table t) ip = match_table t ip"

fun match_hostlist :: "host list \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_hostlist [] _ = False" |
"match_hostlist (h#hs) ip = (match_host h ip \<or> match_hostlist hs ip)"

fun match_hostspec:: "hostspec \<Rightarrow> ('i::len word) \<Rightarrow> bool" where
"match_hostspec AnyHost _ = True" |
"match_hostspec NoRoute _ = True" | (* TODO: unknown *)
"match_hostspec UrpfFailed _ = True" | (* TODO: unknown *)
"match_hostspec Self _ = True" | (* TODO: unknown *)
"match_hostspec (Host hostlist) ip = match_hostlist hostlist ip" |
"match_hostspec (Route route) _ = True" (* TODO: unknown *)

*)

fun lookup_port :: "identifier \<Rightarrow> 16 word" where
"lookup_port (Name n) = 0" | -- TODO
"lookup_port (Number n) = of_nat n"

(* fun match_unary_op :: "(identifier \<Rightarrow> 'a) \<Rightarrow> unary_op \<Rightarrow> 'a \<Rightarrow> bool" where *)
fun match_unary_op :: "(identifier \<Rightarrow> 16 word) \<Rightarrow> unary_op \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_unary_op lookup (Eq i) x = (x = lookup i)" |
"match_unary_op lookup (NEq i) x = (x \<noteq> lookup i)" |
"match_unary_op lookup (Lt i) x = (x < lookup i)" |
"match_unary_op lookup (LtEq i) x = (x \<le> lookup i)" |
"match_unary_op lookup (Gt i) x = (x > lookup i)" |
"match_unary_op lookup (GtEq i) x = (x \<ge> lookup i)"

(* fun match_binary_op :: "(identifier \<Rightarrow> 'a) \<Rightarrow> binary_op \<Rightarrow> 'a \<Rightarrow> bool" where *)
fun match_binary_op :: "binary_op \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_binary_op (RangeIncl l u) x = (of_nat l \<le> x \<and> x \<le> of_nat u)"|
"match_binary_op (RangeExcl l u) x = (of_nat l < x \<and> x < of_nat u)"|
"match_binary_op (RangeComp l u) x = ((l \<le> u) \<and> \<not>(of_nat l \<le> x \<and> x \<le> of_nat u))"

(* fun match_op :: "(identifier \<Rightarrow> 'i) \<Rightarrow> opspec \<Rightarrow> 'i \<Rightarrow> bool" where *)
fun match_op :: "(identifier \<Rightarrow> 16 word) \<Rightarrow> opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_op lookup (Unary operator) x = match_unary_op lookup operator x" |
"match_op lookup (Binary operator) x = match_binary_op operator x"

fun match_op_port :: "opspec \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_op_port opspec p = match_op lookup_port opspec p"

fun match_port_ops :: "opspec list \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port_ops [] _ = False" |
"match_port_ops (operator#ops) p = (match_op_port operator p \<or> match_port_ops ops p)"

fun match_port :: "opspec list option \<Rightarrow> 16 word \<Rightarrow> bool" where
"match_port None _ = True"|
"match_port (Some ops) port = match_port_ops ops port"

(* TODO ipv4 ipv6 versions
fun match_hosts :: "hosts \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_hosts AllHosts _ = True" |
"match_hosts (FromTo from sports to dports) p = (match_hostspec from (p_src p) \<and> match_port sports (p_sport p) \<and> match_hostspec to (p_dst p) \<and> match_port dports (p_dport p))"
*)

fun match_filteropts :: "filteropt list \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"match_filteropts _ _ = True"

datatype 'i::len common_primitive =
IIface "iface"
| OIface "iface"
| Af "afspec"
| Proto "primitive_protocol list"
| Hosts "hosts"

(* TODO ipv4 ipv6 versions
fun matcher :: "'i::len common_primitive \<Rightarrow> 32 simple_packet \<Rightarrow> bool" where
"matcher (IIface iface) p = match_iiface iface p"|
"matcher (OIface iface) p = match_oiface iface p"|
"matcher (Af af) p = match_af af p"|
"matcher (Proto proto) p = match_proto proto p"|
"matcher (Hosts hosts) p = match_hosts hosts p"
*)

end