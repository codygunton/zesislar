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
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00a4Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00a4Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00b8Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt00a4_LoopClass0 -> fp_machineAt00b8_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_13 (args : NextUint64Args) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt00a4_LoopClass0_Hist (args) (returnAddress) (call_after))
    (fp_machineAt00b8_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt00a4_LoopClass0_Hist in Hh.
  destruct Hh as (HF0 & HF1 & HF2 & HF3).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00b8_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

Global Instance zesu_hist_reveal_0 (args : NextUint64Args) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt00a4_LoopClass0_Hist (args) (returnAddress) (call_after)) (((0 < bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) -> bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) <= 8 -> nextInputPointer (nextUint64Base args) <= bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call_after (BV 8%N 0%Z)) (List.nth 6%nat call_after (BV 8%N 0%Z))) (List.nth 5%nat call_after (BV 8%N 0%Z))) (List.nth 4%nat call_after (BV 8%N 0%Z))) (List.nth 3%nat call_after (BV 8%N 0%Z))) (List.nth 2%nat call_after (BV 8%N 0%Z))) (List.nth 1%nat call_after (BV 8%N 0%Z))) (List.nth 0%nat call_after (BV 8%N 0%Z))) /\ bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call_after (BV 8%N 0%Z)) (List.nth 6%nat call_after (BV 8%N 0%Z))) (List.nth 5%nat call_after (BV 8%N 0%Z))) (List.nth 4%nat call_after (BV 8%N 0%Z))) (List.nth 3%nat call_after (BV 8%N 0%Z))) (List.nth 2%nat call_after (BV 8%N 0%Z))) (List.nth 1%nat call_after (BV 8%N 0%Z))) (List.nth 0%nat call_after (BV 8%N 0%Z))) + bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) <= nextInputPointer (nextUint64Base args) + Z.of_nat (length (nextInputBytes (nextUint64Base args))))%Z)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt00a4_LoopClass0_Hist in Hh.
  destruct Hh as (HF0 & HF1 & HF2 & HF3).
  exact HF0.
Qed.

End edges.
