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
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04b0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ccEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04ccStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0510Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0510Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt04b0_ForwardA0N0 -> fp_machineAt04cc_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_116 (args : ParentHeaderArgs) (returnAddress : Z) (call17_result : NextUint64Return) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt04b0_ForwardA0N0_Hist (args) (returnAddress) (call17_result) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after))
    (fp_machineAt04cc_ForwardA0N0_Hist (args) (returnAddress) (call17_result) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt04b0_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt04cc_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_cbcac9df79b9221c, (BV 64%N 0%Z).
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
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF35|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [exact HF26|].
  split; [exact HF27|].
  split; [exact HF28|].
  split; [exact HF29|].
  split; [exact HF30|].
  split; [exact HF31|].
  split; [exact HF32|].
  split; [exact HF33|].
  split; [exact HF34|].
  split; [exact HF36|].
  split; [exact HF37|].
  by vm_compute.
Qed.

(* fp_machineAt04b0_ForwardA0N0 -> fp_machineAt0510_slot0_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_117 (args : ParentHeaderArgs) (returnAddress : Z) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call17_kept_x19 : bv 64) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt04b0_ForwardA0N0_Hist (args) (returnAddress) (call17_result) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after))
    (fp_machineAt0510_slot0_ForwardA0N0_Hist (args) (returnAddress) (call17_result) (call17_word_1_0) (call17_word_1_8) (call17_kept_x19) (call16_after) (call13_after) (call10_after) (call_after))
    (⌜((bool_decide (call17_word_1_8 = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned call17_word_1_8) = (0%Z))%Z))⌝ ∗ ⌜((List.length call14_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call13_after (BV 8%N 0%Z)) (List.nth 30%nat call13_after (BV 8%N 0%Z))) (List.nth 29%nat call13_after (BV 8%N 0%Z))) (List.nth 28%nat call13_after (BV 8%N 0%Z))) (List.nth 27%nat call13_after (BV 8%N 0%Z))) (List.nth 26%nat call13_after (BV 8%N 0%Z))) (List.nth 25%nat call13_after (BV 8%N 0%Z))) (List.nth 24%nat call13_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call13_after (BV 8%N 0%Z)) (List.nth 30%nat call13_after (BV 8%N 0%Z))) (List.nth 29%nat call13_after (BV 8%N 0%Z))) (List.nth 28%nat call13_after (BV 8%N 0%Z))) (List.nth 27%nat call13_after (BV 8%N 0%Z))) (List.nth 26%nat call13_after (BV 8%N 0%Z))) (List.nth 25%nat call13_after (BV 8%N 0%Z))) (List.nth 24%nat call13_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((List.length call15_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call14_after (BV 8%N 0%Z)) (List.nth 30%nat call14_after (BV 8%N 0%Z))) (List.nth 29%nat call14_after (BV 8%N 0%Z))) (List.nth 28%nat call14_after (BV 8%N 0%Z))) (List.nth 27%nat call14_after (BV 8%N 0%Z))) (List.nth 26%nat call14_after (BV 8%N 0%Z))) (List.nth 25%nat call14_after (BV 8%N 0%Z))) (List.nth 24%nat call14_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call14_after (BV 8%N 0%Z)) (List.nth 30%nat call14_after (BV 8%N 0%Z))) (List.nth 29%nat call14_after (BV 8%N 0%Z))) (List.nth 28%nat call14_after (BV 8%N 0%Z))) (List.nth 27%nat call14_after (BV 8%N 0%Z))) (List.nth 26%nat call14_after (BV 8%N 0%Z))) (List.nth 25%nat call14_after (BV 8%N 0%Z))) (List.nth 24%nat call14_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call15_after (BV 8%N 0%Z)) (List.nth 30%nat call15_after (BV 8%N 0%Z))) (List.nth 29%nat call15_after (BV 8%N 0%Z))) (List.nth 28%nat call15_after (BV 8%N 0%Z))) (List.nth 27%nat call15_after (BV 8%N 0%Z))) (List.nth 26%nat call15_after (BV 8%N 0%Z))) (List.nth 25%nat call15_after (BV 8%N 0%Z))) (List.nth 24%nat call15_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call15_after (BV 8%N 0%Z)) (List.nth 30%nat call15_after (BV 8%N 0%Z))) (List.nth 29%nat call15_after (BV 8%N 0%Z))) (List.nth 28%nat call15_after (BV 8%N 0%Z))) (List.nth 27%nat call15_after (BV 8%N 0%Z))) (List.nth 26%nat call15_after (BV 8%N 0%Z))) (List.nth 25%nat call15_after (BV 8%N 0%Z))) (List.nth 24%nat call15_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call17_kept_x19 (bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))))⌝ ∗ ⌜(∃ (call17_arg_x13 : bv 64) (call17_arg_x14 : bv 64) (call17_arg_x15 : bv 64) (call17_arg_x16 : bv 64) (call17_arg_x17 : bv 64), (Z.of_nat (length (take (Z.to_nat (bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))))) (drop (Z.to_nat (bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))) = bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))))) /\ (nextUint64CallDomain
          (nextUint64CallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551360%Z))); ((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551264%Z))); ((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))); (call17_arg_x13); (call17_arg_x14); (call17_arg_x15); (call17_arg_x16); (call17_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) (((parentHeaderInputEnd args))) (take (Z.to_nat (bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))))) (drop (Z.to_nat (bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))))) /\ (nextUint64CallResult
            (nextUint64Base
              (nextUint64CallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551360%Z))); ((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551264%Z))); ((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))); (call17_arg_x13); (call17_arg_x14); (call17_arg_x15); (call17_arg_x16); (call17_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) (((parentHeaderInputEnd args))) (take (Z.to_nat (bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))))) (drop (Z.to_nat (bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))))
            (call17_result)) /\ (call17_word_1_0 = Z_to_bv 64 (nextRestPointer (call17_result))) /\ (call17_word_1_8 = Z_to_bv 64 (nextRestLength (call17_result))))⌝ ∗ ⌜((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) /\ bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) + bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt04b0_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV5 & %HV6 & %HV7 & %HV8 & %HV9 & %HV10 & %HV12 & %HV13 & %HV15 & %HV16 & %HV17 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0510_slot0_ForwardA0N0_Hist.
  exists call16_kept_x18, call16_kept_x19, call15_after, call15_kept_x18, call15_kept_x19, call14_after, call14_kept_x18, call14_kept_x19, call13_kept_x18, call13_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_cbcac9df79b9221c, (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HV5|].
  split; [exact HV6|].
  split; [exact HV7|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HV8|].
  split; [exact HV9|].
  split; [exact HV10|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HV12|].
  split; [exact HV13|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HV15|].
  split; [exact HV16|].
  split; [exact HV17|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF35|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [exact HF26|].
  split; [exact HF27|].
  split; [exact HF28|].
  split; [exact HF29|].
  split; [exact HF30|].
  split; [exact HF31|].
  split; [exact HF32|].
  split; [exact HF33|].
  split; [exact HF34|].
  split; [exact HF36|].
  split; [exact HF37|].
  split; [by vm_compute|].
  exact HN0.
Qed.

End edges.
