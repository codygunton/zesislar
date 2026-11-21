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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0558Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0558Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0568Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0568Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0558_ForwardA0N0 -> fp_machineAt0568_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_131 (args : ParentHeaderArgs) (returnAddress : Z) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0558_ForwardA0N0_Hist (args) (returnAddress) (call18_after) (call17_result) (call17_word_1_0) (call17_word_1_8) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (fp_machineAt0568_ForwardA0N0_Hist (args) (returnAddress) (call18_after) (call17_result) (call17_word_1_0) (call17_word_1_8) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (⌜(∃ (call18_arg_x13 : bv 64) (call18_arg_x14 : bv 64) (call18_arg_x15 : bv 64) (call18_arg_x16 : bv 64) (call18_arg_x17 : bv 64) (call18_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551392%Z))); (call17_word_1_0); (call17_word_1_8); (call18_arg_x13); (call18_arg_x14); (call18_arg_x15); (call18_arg_x16); (call18_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call17_word_1_8))) (drop (Z.to_nat (bv_unsigned (call17_word_1_0) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call18_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551392%Z))); (call17_word_1_0); (call17_word_1_8); (call18_arg_x13); (call18_arg_x14); (call18_arg_x15); (call18_arg_x16); (call18_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call17_word_1_8))) (drop (Z.to_nat (bv_unsigned (call17_word_1_0) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call18_before) (call18_after)))⌝ ∗ ⌜((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call17_word_1_0) /\ bv_unsigned (call17_word_1_0) + bv_unsigned (call17_word_1_8) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0558_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_d77b5950a2aea933 & forward_witness_751588b52f8a71ff & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & forward_witness_9644ccf41f39915a & forward_witness_1492ef7bd46b3b7a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41).
  iIntros "HN".
  iDestruct "HN" as "(%HV18 & %HV19 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0568_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_d77b5950a2aea933, forward_witness_751588b52f8a71ff, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_cbcac9df79b9221c, forward_witness_9644ccf41f39915a, forward_witness_1492ef7bd46b3b7a, (BV 64%N 0%Z).
  split; [exact HF0|].
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
  split; [exact HV18|].
  split; [exact HV19|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [exact HF25|].
  split; [exact HF26|].
  split; [exact HF27|].
  split; [exact HF28|].
  split; [exact HF29|].
  split; [exact HF30|].
  split; [exact HF31|].
  split; [exact HF32|].
  split; [exact HF33|].
  split; [exact HF34|].
  split; [exact HF35|].
  split; [exact HF36|].
  split; [exact HF39|].
  split; [exact HF40|].
  split; [exact HF41|].
  split; [by vm_compute|].
  exact HF37.
Qed.

End edges.
