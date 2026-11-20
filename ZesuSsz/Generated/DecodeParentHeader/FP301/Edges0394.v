(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0394Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0394Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot039cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot039cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0394_ForwardA0N0 -> fp_machineAt039c_LoopClass0 (loop_entry) *)
Global Instance zesu_hist_edge_90 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0394_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call10_after) (call_after))
    (fp_machineAt039c_LoopClass0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call10_after) (call_after))
    (⌜((negb (bool_decide ((bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call13_after (BV 8%N 0%Z)) (List.nth 14%nat call13_after (BV 8%N 0%Z))) (List.nth 13%nat call13_after (BV 8%N 0%Z))) (List.nth 12%nat call13_after (BV 8%N 0%Z))) (List.nth 11%nat call13_after (BV 8%N 0%Z))) (List.nth 10%nat call13_after (BV 8%N 0%Z))) (List.nth 9%nat call13_after (BV 8%N 0%Z))) (List.nth 8%nat call13_after (BV 8%N 0%Z))) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call13_after (BV 8%N 0%Z)) (List.nth 14%nat call13_after (BV 8%N 0%Z))) (List.nth 13%nat call13_after (BV 8%N 0%Z))) (List.nth 12%nat call13_after (BV 8%N 0%Z))) (List.nth 11%nat call13_after (BV 8%N 0%Z))) (List.nth 10%nat call13_after (BV 8%N 0%Z))) (List.nth 9%nat call13_after (BV 8%N 0%Z))) (List.nth 8%nat call13_after (BV 8%N 0%Z)))) <> (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0394_ForwardA0N0_Hist in Hh.
  destruct Hh as (call12_kept_x20 & call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26).
  iIntros "HN".
  iDestruct "HN" as "(%HV10 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt039c_LoopClass0_Hist.
  exists call12_kept_x20, call11_kept_x19.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact (proj1 HF11)|].
  split; [exact (proj1 HF14)|].
  split; [exact (proj1 HF16)|].
  split; [exact (proj1 HF20)|].
  split; [exact (proj1 HF21)|].
  split; [exact (proj1 HF22)|].
  split; [exact (proj1 HF25)|].
  split; [exact (proj1 HF26)|].
  exact (proj1 HV10).
Qed.

End edges.
