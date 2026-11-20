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
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot009cEntries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot009cStructural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00a4Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot00a4Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt009c_ForwardA0N0 -> fp_machineAt00a4_LoopClass0 (loop_entry) *)
Global Instance zesu_hist_edge_11 (args : NextUint64Args) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt009c_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (fp_machineAt00a4_LoopClass0_Hist (args) (returnAddress) (call_after))
    (⌜((0 < bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) -> bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) <= 8 -> nextInputPointer (nextUint64Base args) <= bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call_after (BV 8%N 0%Z)) (List.nth 6%nat call_after (BV 8%N 0%Z))) (List.nth 5%nat call_after (BV 8%N 0%Z))) (List.nth 4%nat call_after (BV 8%N 0%Z))) (List.nth 3%nat call_after (BV 8%N 0%Z))) (List.nth 2%nat call_after (BV 8%N 0%Z))) (List.nth 1%nat call_after (BV 8%N 0%Z))) (List.nth 0%nat call_after (BV 8%N 0%Z))) /\ bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call_after (BV 8%N 0%Z)) (List.nth 6%nat call_after (BV 8%N 0%Z))) (List.nth 5%nat call_after (BV 8%N 0%Z))) (List.nth 4%nat call_after (BV 8%N 0%Z))) (List.nth 3%nat call_after (BV 8%N 0%Z))) (List.nth 2%nat call_after (BV 8%N 0%Z))) (List.nth 1%nat call_after (BV 8%N 0%Z))) (List.nth 0%nat call_after (BV 8%N 0%Z))) + bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) <= nextInputPointer (nextUint64Base args) + Z.of_nat (length (nextInputBytes (nextUint64Base args))))%Z)⌝ ∗ ⌜((negb (bool_decide ((bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z)))) <> (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt009c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_9644ccf41f39915a & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16).
  iIntros "HN".
  iDestruct "HN" as "(%HV4 & %HV6 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00a4_LoopClass0_Hist.
  split; [exact HV4|].
  split; [exact (proj1 HF10)|].
  split; [exact (proj1 HF13)|].
  exact (proj1 HV6).
Qed.

End edges.
