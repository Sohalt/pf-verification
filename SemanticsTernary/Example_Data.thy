theory Example_Data
  imports          
          "../PF_Firewall_Common"
          "../PF_Primitives"
begin
(*
int_if  = "dc0"
lan_net = "192.168.0.0/24"

# table containing all IP addresses assigned to the firewall
table <firewall> const { self }

# don't filter on the loopback interface
set skip on lo0

# scrub incoming packets
match in all scrub (no-df)

# set up a default deny policy
block all

# activate spoofing protection for all interfaces
block in quick from urpf-failed

# only allow ssh connections from the local network if it's from the
# trusted computer, 192.168.0.15. use "block return" so that a TCP RST is
# sent to close blocked connections right away. use "quick" so that this
# rule is not overridden by the "pass" rules below.
block return in quick on $int_if proto tcp from ! 192.168.0.15 to $int_if port ssh

# pass all traffic to and from the local network.
# these rules will create state entries due to the default
# "keep state" option which will automatically be applied.
pass in  on $int_if from $lan_net
pass out on $int_if to   $lan_net

# pass tcp, udp, and icmp out on the external (Internet) interface.
# tcp connections will be modulated, udp/icmp will be tracked statefully.
pass out on egress proto { tcp udp icmp } all modulate state

# allow ssh connections in on the external interface as long as they're
# NOT destined for the firewall (i.e., they're destined for a machine on
# the local network). log the initial packet so that we can later tell
# who is trying to connect.
# Uncomment last part to use the tcp syn proxy to proxy the connection.
pass in log on egress proto tcp to ! <firewall> port ssh # synproxy state

*)


definition pf_ruleset ::"PF_Primitives.common_primitive PF_Firewall_Common.ruleset" where
"pf_ruleset = [
(PfRule \<lparr>get_action = Block, get_quick = False, get_match = MatchAny\<rparr>),
(PfRule \<lparr>get_action = Block, get_quick = True, get_match = (MatchAnd (Match (Src UrpfFailed)) (Match (Interface None (Some In))))\<rparr>),
(PfRule \<lparr>get_action = Block, get_quick = True, get_match =
(MatchAnd (Match (Interface (Some (InterfaceName ''dc0'')) (Some In)))
(MatchAnd (Match (Protocol (Proto TCP)))
(MatchAnd (MatchNot (Match (Src (Hostspec (Address (IPv4 (PrefixMatch (ipv4addr_of_dotdecimal (192, 168, 0, 15)) 32)))))))
(MatchAnd (Match (Dst (Address (IPv4 (PrefixMatch (ipv4addr_of_dotdecimal (192, 168, 0, 1)) 32)))))
(Match (Dst_Ports (L4Ports TCP (Unary (Eq 22)))))))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc0'')) (Some In)))
     (Match (Src (Hostspec (Address (IPv4 (PrefixMatch (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 24)))))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc0'')) (Some Out)))
     (Match (Dst (Address (IPv4 (PrefixMatch (ipv4addr_of_dotdecimal (192, 168, 0, 0)) 24))))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc0'')) (Some Out)))
     (Match (Protocol (Proto TCP))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc0'')) (Some Out)))
     (Match (Protocol (Proto UDP))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc0'')) (Some Out)))
     (Match (Protocol (Proto ICMP))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc1'')) (Some Out)))
     (Match (Protocol (Proto TCP))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc1'')) (Some Out)))
     (Match (Protocol (Proto UDP))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match = (MatchAnd (Match (Interface (Some (InterfaceName ''dc1'')) (Some Out)))
     (Match (Protocol (Proto ICMP))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match =
(MatchAnd (Match (Interface (Some (InterfaceName ''dc0'')) (Some In)))
(MatchAnd (Match (Protocol (Proto TCP)))
(MatchAnd (Match (Dst (Table ''firewall'')))
(Match (Dst_Ports (L4Ports TCP (Unary (Eq 22))))))))\<rparr>),
(PfRule \<lparr>get_action = Pass, get_quick = False, get_match =
(MatchAnd (Match (Interface (Some (InterfaceName ''dc1'')) (Some In)))
(MatchAnd (Match (Protocol (Proto TCP)))
(MatchAnd (Match (Dst (Table ''firewall'')))
(Match (Dst_Ports (L4Ports TCP (Unary (Eq 22))))))))\<rparr>)]"

definition pf_context ::"pfcontext" where
"pf_context = \<lparr>get_tables = map_of [(''firewall'',
[(TableEntry (IPv4 (PrefixMatch (ipv4addr_of_dotdecimal (127, 0, 0, 1)) 32))),
(TableEntry (IPv4 (PrefixMatch (ipv4addr_of_dotdecimal (192, 168, 0, 1)) 32))),
(TableEntry (IPv4 (PrefixMatch (ipv4addr_of_dotdecimal (1, 2, 3, 4)) 32)))])]\<rparr>"

end