(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Export ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0070Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0070Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt00b8_ForwardA0N0 -> fp_machineAt0070_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_14 (args : NextUint64Args) (returnAddress : Z) (join_resource_31_bytes : list byte) (join_resource_32_bytes : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt00b8_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt0070_ForwardA0N0_Hist (args) (returnAddress) (join_resource_31_bytes) (join_resource_32_bytes))
    (⌜(∃ result : NextUint64Return, nextResultBytes result = join_resource_32_bytes /\ join_resource_31_bytes = nextUint64SliceImage (nextRestPointer result) (nextRestLength result) /\ nextUint64RootResult (nextUint64Base args) result)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt00b8_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_9644ccf41f39915a & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0070_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_9644ccf41f39915a, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_791c5acc1109e8e6, (BV 64%N 0%Z).
  split; [exact HN0|].
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  by vm_compute.
Qed.

End edges.
