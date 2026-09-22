(* Rule set v2 without the spec table.

   The table answers a load instruction with `zesu_ld_spec`, whose
   precondition wants a bare word, and a block that loads out of an array
   cannot meet it. This file measures the difference. *)

Require Import ZesuSsz.Automation.Sets.v1.
Require Import ZesuSsz.Automation.TraceTailLemmas.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.Switch.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.WordArrayBytes.
Require Import ZesuSsz.Automation.StackArrayLookup.
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import ZesuSsz.Automation.LookupReduce.
Require Import ZesuSsz.Automation.CallReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
