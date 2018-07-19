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


definition match_table_v4_inner :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4_inner table addr =
 (case (find (\<lambda> t . prefix_match_semantics (ip4 (ta t)) addr) table) of
 (Some t) \<Rightarrow> decision t |None \<Rightarrow> False)"

definition match_table_v4 :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4 table addr = match_table_v4_inner (sort [t \<leftarrow> table. isIPv4 (ta t)]) addr"


abbreviation foldf :: "table_entry \<Rightarrow> 32 word set \<Rightarrow> 32 word set" where
"foldf t a \<equiv> (case t of (TableEntry te) \<Rightarrow> a \<union> prefix_to_wordset (ip4 te) | (TableEntryNegated te) \<Rightarrow> a - prefix_to_wordset  (ip4 te))"

definition table_to_set_v4 :: "table \<Rightarrow> 32 word set" where
"table_to_set_v4 table = foldr foldf table {}"

definition match_table_v4'_inner :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4'_inner table address \<longleftrightarrow> address \<in> table_to_set_v4 table"

definition match_table_v4' :: "table \<Rightarrow> 32 word \<Rightarrow> bool" where
"match_table_v4' table address = match_table_v4'_inner (sort [t \<leftarrow> table. isIPv4 (ta t)]) address"


definition valid_table :: "table \<Rightarrow> bool" where
"valid_table table \<longleftrightarrow> (\<forall> t \<in> set table . (case (ta t) of (IPv4 a) \<Rightarrow> valid_prefix a | (IPv6 a) \<Rightarrow> valid_prefix a))"


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