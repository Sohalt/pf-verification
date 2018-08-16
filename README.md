# Verified Firewall Analysis of BSD PF

This repository contains a formal semantics of the BSD PF firewall in Isabelle/HOL, along with transformations to turn a PF ruleset into
an iptables ruleset approximating the PF ruleset. The transformations are proven sound w.r.t. the filtering semantics.

All files/theories have a "PF_" prefix so they do not clash with theories of the same name from the `Iptables_Semantics` theories.

`PF_PF.thy` contains the filtering semantics.

`SemanticsTernary/PF_Semantics_Ternary.thy` contains an approximate filtering semantics using ternary logic.

`SemanticsTernary/PF_PF_To_Iptables.thy`	contains the translation from PF to iptables along with the main theorem, proving that the transformation preserves the semantics.

`SemanticsTernary/PF_Example.thy`	contains an example PF firewall translated to iptables.
