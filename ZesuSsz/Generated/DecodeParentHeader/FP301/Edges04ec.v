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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ecEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ecStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt04ec_ForwardA0N0 -> fp_machineAt00b0_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_121 (args : ParentHeaderArgs) (returnAddress : Z) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call16_after : DecodeItemOutcome) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x10 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt04ec_ForwardA0N0_Hist (args) (returnAddress) (call18_after) (call17_result) (call17_word_1_0) (call17_word_1_8) (call16_after) (call13_after) (call10_after) (call_after))
    (fp_machineAt00b0_ForwardA0N0_Hist (args) (returnAddress) (machine_x10))
    (⌜((2148617472%Z <= bv_unsigned machine_x10 <= 2148618660%Z)%Z)⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10 >= bv_unsigned (BV 64%N 2148617472%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10) >= (2148617472%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10 <= bv_unsigned (BV 64%N 2148618660%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10) <= (2148618660%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt04ec_ForwardA0N0_Hist in Hh.
  destruct Hh as (call17_kept_x19 & call16_kept_x18 & call16_kept_x19 & call15_after & call15_kept_x18 & call15_kept_x19 & call14_after & call14_kept_x18 & call14_kept_x19 & call13_kept_x18 & call13_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_d77b5950a2aea933 & forward_witness_751588b52f8a71ff & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00b0_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, (BV 64%N 0%Z), forward_witness_d77b5950a2aea933.
  split; [exact HN0|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [exact HF25|].
  split; [exact HF26|].
  split; [exact HF37|].
  split; [by vm_compute|].
  split; [exact HF28|].
  split; [exact HF48|].
  split; [exact HF49|].
  split; [exact HN1|].
  exact HN2.
Qed.

Global Instance zesu_hist_reveal_56 (args : ParentHeaderArgs) (returnAddress : Z) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call16_after : DecodeItemOutcome) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt04ec_ForwardA0N0_Hist (args) (returnAddress) (call18_after) (call17_result) (call17_word_1_0) (call17_word_1_8) (call16_after) (call13_after) (call10_after) (call_after)) ((∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before) (call_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt04ec_ForwardA0N0_Hist in Hh.
  destruct Hh as (call17_kept_x19 & call16_kept_x18 & call16_kept_x19 & call15_after & call15_kept_x18 & call15_kept_x19 & call14_after & call14_kept_x18 & call14_kept_x19 & call13_kept_x18 & call13_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_d77b5950a2aea933 & forward_witness_751588b52f8a71ff & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50).
  exact HF0.
Qed.

End edges.
