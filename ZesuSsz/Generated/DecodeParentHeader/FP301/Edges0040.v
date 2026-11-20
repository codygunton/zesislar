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
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0040Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0040Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0048Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0048Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0054Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0040_ForwardA0N0 -> fp_machineAt0048_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_1 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0040_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt0048_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (⌜((negb (bool_decide ((bv_zero_extend 64%N (bv_concat 16%N (List.nth 33%nat call_after (BV 8%N 0%Z)) (List.nth 32%nat call_after (BV 8%N 0%Z)))) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_concat 16%N (List.nth 33%nat call_after (BV 8%N 0%Z)) (List.nth 32%nat call_after (BV 8%N 0%Z)))) <> (0%Z))%Z))⌝ ∗ ⌜(∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before) (call_after)))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0040_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV3 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0048_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, (BV 64%N 0%Z).
  split; [exact HV3|].
  split; [by vm_compute|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HN0.
Qed.

(* fp_machineAt0040_ForwardA0N0 -> fp_machineAt0054_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_2 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0040_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt0054_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (⌜((bool_decide ((bv_zero_extend 64%N (bv_concat 16%N (List.nth 33%nat call_after (BV 8%N 0%Z)) (List.nth 32%nat call_after (BV 8%N 0%Z)))) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_concat 16%N (List.nth 33%nat call_after (BV 8%N 0%Z)) (List.nth 32%nat call_after (BV 8%N 0%Z)))) = (0%Z))%Z))⌝ ∗ ⌜(∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before) (call_after)))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0040_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV3 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0054_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, (BV 64%N 0%Z).
  split; [exact HV3|].
  split; [by vm_compute|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HN0.
Qed.

End edges.
