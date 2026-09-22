(* The rule file a probe loads to measure rule set v2.

   `infer_boundary.py --rule` inlines this into the probe, so nothing
   here is installed in the automation: a probe says whether a rule is
   affordable before a gate is paid for. *)

Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
