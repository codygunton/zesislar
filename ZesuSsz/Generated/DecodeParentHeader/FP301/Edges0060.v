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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0060Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0060Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0068Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0068Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Structural.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeObligations.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0060_ForwardA0N0 -> fp_machineAt0068_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_6 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (fp_machineAt0068_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0068_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, (BV 64%N 0%Z).
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  by vm_compute.
Qed.

Global Instance zesu_hist_reveal_1 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after)) ((∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before) (call_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  exact HF0.
Qed.

Global Instance zesu_hist_reveal_2 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z)) /\ ((((0%Z) <= (bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))))%Z)) /\ ((((bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))) <= (255%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  exact HF12.
Qed.

Global Instance zesu_hist_reveal_3 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  exact (proj1 HF12).
Qed.

Global Instance zesu_hist_reveal_4 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  exact (proj1 (proj2 HF12)).
Qed.

Global Instance zesu_hist_reveal_5 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((((0%Z) <= (bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  exact (proj1 (proj2 (proj2 HF12))).
Qed.

Global Instance zesu_hist_reveal_6 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((((bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))) <= (255%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  exact (proj2 (proj2 (proj2 HF12))).
Qed.

(* fp_machineAt0060_ForwardA0N0 -> fp_machineAt00a8_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_7 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0060_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (fp_machineAt00a8_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (⌜(bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args)⌝ ∗ ⌜((bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((List.length call_after = 40)%nat)⌝ ∗ ⌜(bool_decide ((bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z))) = (BV 64%N 0%Z))) = true⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. pose proof Hh as HS. unfold fp_machineAt0060_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12).
  iIntros "HN".
  iDestruct "HN" as "(%HV0 & %HV1 & %HV2 & %HG0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00a8_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact (fp_edge0060_00a8_CandidateError_holds args returnAddress call_after HS HV0 HV1 HV2 HG0)|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [by vm_compute|].
  split; [exact HF1|].
  exact HF7.
Qed.

End edges.
