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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04a8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04a8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04b0Structural.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeObligations.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt04a8_ForwardA0N0 -> fp_machineAt0270_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_121 (args : ParentHeaderArgs) (returnAddress : Z) (call17_result : NextUint64Return) (call17_kept_x19 : bv 64) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) (machine_x10 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt04a8_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (fp_machineAt0270_ForwardA0N0_Hist (args) (returnAddress) (machine_x10) (call10_after) (call_after))
    (⌜((0%Z <= bv_unsigned machine_x10 <= 65535%Z)%Z)⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10 >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10 <= bv_unsigned (BV 64%N 65535%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10) <= (65535%Z))%Z))⌝ ∗ ⌜(bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args)⌝ ∗ ⌜((bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((List.length call_after = 40)%nat)⌝ ∗ ⌜((List.length call10_after = 40)%nat)⌝ ∗ ⌜((List.length call13_after = 40)%nat)⌝ ∗ ⌜((List.length call14_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call13_after (BV 8%N 0%Z)) (List.nth 30%nat call13_after (BV 8%N 0%Z))) (List.nth 29%nat call13_after (BV 8%N 0%Z))) (List.nth 28%nat call13_after (BV 8%N 0%Z))) (List.nth 27%nat call13_after (BV 8%N 0%Z))) (List.nth 26%nat call13_after (BV 8%N 0%Z))) (List.nth 25%nat call13_after (BV 8%N 0%Z))) (List.nth 24%nat call13_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call13_after (BV 8%N 0%Z)) (List.nth 30%nat call13_after (BV 8%N 0%Z))) (List.nth 29%nat call13_after (BV 8%N 0%Z))) (List.nth 28%nat call13_after (BV 8%N 0%Z))) (List.nth 27%nat call13_after (BV 8%N 0%Z))) (List.nth 26%nat call13_after (BV 8%N 0%Z))) (List.nth 25%nat call13_after (BV 8%N 0%Z))) (List.nth 24%nat call13_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((List.length call15_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call14_after (BV 8%N 0%Z)) (List.nth 30%nat call14_after (BV 8%N 0%Z))) (List.nth 29%nat call14_after (BV 8%N 0%Z))) (List.nth 28%nat call14_after (BV 8%N 0%Z))) (List.nth 27%nat call14_after (BV 8%N 0%Z))) (List.nth 26%nat call14_after (BV 8%N 0%Z))) (List.nth 25%nat call14_after (BV 8%N 0%Z))) (List.nth 24%nat call14_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call14_after (BV 8%N 0%Z)) (List.nth 30%nat call14_after (BV 8%N 0%Z))) (List.nth 29%nat call14_after (BV 8%N 0%Z))) (List.nth 28%nat call14_after (BV 8%N 0%Z))) (List.nth 27%nat call14_after (BV 8%N 0%Z))) (List.nth 26%nat call14_after (BV 8%N 0%Z))) (List.nth 25%nat call14_after (BV 8%N 0%Z))) (List.nth 24%nat call14_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((List.length call16_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call15_after (BV 8%N 0%Z)) (List.nth 30%nat call15_after (BV 8%N 0%Z))) (List.nth 29%nat call15_after (BV 8%N 0%Z))) (List.nth 28%nat call15_after (BV 8%N 0%Z))) (List.nth 27%nat call15_after (BV 8%N 0%Z))) (List.nth 26%nat call15_after (BV 8%N 0%Z))) (List.nth 25%nat call15_after (BV 8%N 0%Z))) (List.nth 24%nat call15_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call15_after (BV 8%N 0%Z)) (List.nth 30%nat call15_after (BV 8%N 0%Z))) (List.nth 29%nat call15_after (BV 8%N 0%Z))) (List.nth 28%nat call15_after (BV 8%N 0%Z))) (List.nth 27%nat call15_after (BV 8%N 0%Z))) (List.nth 26%nat call15_after (BV 8%N 0%Z))) (List.nth 25%nat call15_after (BV 8%N 0%Z))) (List.nth 24%nat call15_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((List.length (nextResultBytes (call17_result)) = 16)%nat)⌝ ∗ ⌜((zesu_named_eq call17_kept_x19 (bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))))⌝ ∗ ⌜(∃ (call17_arg_x13 : bv 64) (call17_arg_x14 : bv 64) (call17_arg_x15 : bv 64) (call17_arg_x16 : bv 64) (call17_arg_x17 : bv 64), (Z.of_nat (length (take (Z.to_nat (bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))))) (drop (Z.to_nat (bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))) = bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))))) /\ (nextUint64CallDomain
          (nextUint64CallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551360%Z))); ((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551264%Z))); ((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))); (call17_arg_x13); (call17_arg_x14); (call17_arg_x15); (call17_arg_x16); (call17_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) (((parentHeaderInputEnd args))) (take (Z.to_nat (bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))))) (drop (Z.to_nat (bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))))) /\ (nextUint64CallResult
            (nextUint64Base
              (nextUint64CallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551360%Z))); ((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551264%Z))); ((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))); (call17_arg_x13); (call17_arg_x14); (call17_arg_x15); (call17_arg_x16); (call17_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) (((parentHeaderInputEnd args))) (take (Z.to_nat (bv_unsigned (((bv_sub call16_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))))) (drop (Z.to_nat (bv_unsigned (((bv_add call16_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))))
            (call17_result)) /\ ((Z_to_bv 64 (nextRestPointer (call17_result))) = Z_to_bv 64 (nextRestPointer (call17_result))) /\ ((Z_to_bv 64 (nextRestLength (call17_result))) = Z_to_bv 64 (nextRestLength (call17_result))))⌝ ∗ ⌜(negb (bool_decide ((bv_zero_extend 64%N (bv_concat 16%N (List.nth 9%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z)) (List.nth 8%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z)))) = (BV 64%N 0%Z)))) = true⌝ ∗ ⌜machine_x10 = (bv_zero_extend 64%N (bv_concat 16%N (List.nth 9%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z)) (List.nth 8%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z))))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. pose proof Hh as HS. unfold fp_machineAt04a8_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HV0 & %HV1 & %HV2 & %HV3 & %HV4 & %HV5 & %HV6 & %HV7 & %HV9 & %HV10 & %HV11 & %HV12 & %HV13 & %HV14 & %HV15 & %HV16 & %HV17 & %HG0 & %HE0 & _)".
  destruct HF1 as (call12_after_HF1 & call12_kept_x18_HF1 & call12_kept_x20_HF1 & call11_kept_x19_HF1 & HF1_0 & HF1_1 & HF1_2 & HF1_3 & HF1_4 & HF1_5 & HF1_6).
  destruct HF1_0 as (call11_after_HF1_0 & call11_kept_x18_HF1_0 & call10_kept_x20_HF1_0 & HF1_0_0 & HF1_0_1 & HF1_0_2 & HF1_0_3 & HF1_0_4 & HF1_0_5 & HF1_0_6 & HF1_0_7).
  destruct HF1_0_0 as (call10_kept_x19_HF1_0_0 & call9_after_HF1_0_0 & call9_kept_x18_HF1_0_0 & call9_kept_x19_HF1_0_0 & call8_after_HF1_0_0 & call8_kept_x18_HF1_0_0 & call8_kept_x19_HF1_0_0 & call7_after_HF1_0_0 & call7_kept_x18_HF1_0_0 & call7_kept_x19_HF1_0_0 & call6_after_HF1_0_0 & call6_kept_x18_HF1_0_0 & call6_kept_x19_HF1_0_0 & call5_after_HF1_0_0 & call5_kept_x18_HF1_0_0 & call5_kept_x19_HF1_0_0 & call4_after_HF1_0_0 & call4_kept_x18_HF1_0_0 & call4_kept_x19_HF1_0_0 & call3_after_HF1_0_0 & call3_kept_x18_HF1_0_0 & call3_kept_x19_HF1_0_0 & call2_after_HF1_0_0 & call2_kept_x18_HF1_0_0 & call2_kept_x19_HF1_0_0 & HF1_0_0_0 & HF1_0_0_1 & HF1_0_0_2 & HF1_0_0_3 & HF1_0_0_4 & HF1_0_0_5 & HF1_0_0_6 & HF1_0_0_7 & HF1_0_0_8 & HF1_0_0_9 & HF1_0_0_10 & HF1_0_0_11 & HF1_0_0_12 & HF1_0_0_13 & HF1_0_0_14 & HF1_0_0_15 & HF1_0_0_16 & HF1_0_0_17 & HF1_0_0_18 & HF1_0_0_19 & HF1_0_0_20 & HF1_0_0_21 & HF1_0_0_22 & HF1_0_0_23 & HF1_0_0_24 & HF1_0_0_25 & HF1_0_0_26 & HF1_0_0_27 & HF1_0_0_28 & HF1_0_0_29 & HF1_0_0_30 & HF1_0_0_31 & HF1_0_0_32 & HF1_0_0_33 & HF1_0_0_34 & HF1_0_0_35 & HF1_0_0_36 & HF1_0_0_37 & HF1_0_0_38 & HF1_0_0_39 & HF1_0_0_40 & HF1_0_0_41 & HF1_0_0_42 & HF1_0_0_43 & HF1_0_0_44).
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0270_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff.
  split; [exact HF0|].
  split; [exact (ex_intro _ call11_after_HF1_0 (ex_intro _ call11_kept_x18_HF1_0 (ex_intro _ call11_kept_x19_HF1 (ex_intro _ call10_kept_x19_HF1_0_0 (ex_intro _ call10_kept_x20_HF1_0 (ex_intro _ call9_after_HF1_0_0 (ex_intro _ call9_kept_x18_HF1_0_0 (ex_intro _ call9_kept_x19_HF1_0_0 (ex_intro _ call8_after_HF1_0_0 (ex_intro _ call8_kept_x18_HF1_0_0 (ex_intro _ call8_kept_x19_HF1_0_0 (ex_intro _ call7_after_HF1_0_0 (ex_intro _ call7_kept_x18_HF1_0_0 (ex_intro _ call7_kept_x19_HF1_0_0 (ex_intro _ call6_after_HF1_0_0 (ex_intro _ call6_kept_x18_HF1_0_0 (ex_intro _ call6_kept_x19_HF1_0_0 (ex_intro _ call5_after_HF1_0_0 (ex_intro _ call5_kept_x18_HF1_0_0 (ex_intro _ call5_kept_x19_HF1_0_0 (ex_intro _ call4_after_HF1_0_0 (ex_intro _ call4_kept_x18_HF1_0_0 (ex_intro _ call4_kept_x19_HF1_0_0 (ex_intro _ call3_after_HF1_0_0 (ex_intro _ call3_kept_x18_HF1_0_0 (ex_intro _ call3_kept_x19_HF1_0_0 (ex_intro _ call2_after_HF1_0_0 (ex_intro _ call2_kept_x18_HF1_0_0 (ex_intro _ call2_kept_x19_HF1_0_0 (conj HF1_0_0_0 (conj HF1_0_0_1 (conj HF1_0_0_2 (conj HF1_0_0_3 (conj HF1_0_0_4 (conj HF1_0_0_5 (conj HF1_0_0_6 (conj HF1_0_0_7 (conj HF1_0_0_8 (conj HF1_0_0_9 (conj HF1_0_0_10 (conj HF1_0_0_11 (conj HF1_0_0_12 (conj HF1_0_0_13 (conj HF1_0_0_14 (conj HF1_0_0_15 (conj HF1_0_0_16 (conj HF1_0_0_17 (conj HF1_0_0_18 (conj HF1_0_0_19 (conj HF1_0_0_20 (conj HF1_0_0_21 (conj HF1_0_0_22 (conj HF1_0_0_23 (conj HF1_0_0_24 (conj HF1_0_0_25 (conj HF1_0_0_26 (conj HF1_0_0_27 (conj HF1_0_0_28 (conj HF1_0_0_29 (conj HF1_0_0_30 (conj HF1_0_0_31 (conj HF1_0_0_32 (conj HF1_0_0_33 (conj HF1_0_0_34 (conj HF1_0_0_35 (conj HF1_0_0_36 (conj HF1_0_0_37 (conj HF1_0_0_38 (conj HF1_0_0_39 (conj HF1_0_0_40 (conj HF1_0_0_41 (conj HF1_0_0_42 (conj HF1_0_0_43 (conj HF1_0_1 (conj HF1_0_0_44 (conj HF1_0_2 (conj HF1_0_3 HF1_0_4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))|].
  split; [exact HN0|].
  split; [exact (fp_edge04a8_0270_CandidateError_holds args returnAddress call17_result (Z_to_bv 64 (nextRestPointer (call17_result))) (Z_to_bv 64 (nextRestLength (call17_result))) call17_kept_x19 call16_after call16_kept_x18 call16_kept_x19 call15_after call15_kept_x18 call15_kept_x19 call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after machine_x21_1 machine_x22_1 HS HV0 HV1 HV2 HV3 HV4 HV5 HV6 HV7 HV9 HV10 HV11 HV12 HV13 HV14 HV15 HV16 HV17 HG0)|].
  split; [exact (fp_edge04a8_0270_ErrorTag_holds args returnAddress call17_result (Z_to_bv 64 (nextRestPointer (call17_result))) (Z_to_bv 64 (nextRestLength (call17_result))) call17_kept_x19 call16_after call16_kept_x18 call16_kept_x19 call15_after call15_kept_x18 call15_kept_x19 call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after machine_x21_1 machine_x22_1 machine_x10 HS HV0 HV1 HV2 HV3 HV4 HV5 HV6 HV7 HV9 HV10 HV11 HV12 HV13 HV14 HV15 HV16 HV17 HG0 HE0)|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF27|].
  split; [exact HF14|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [exact HN1|].
  exact HN2.
Qed.

(* fp_machineAt04a8_ForwardA0N0 -> fp_machineAt04b0_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_122 (args : ParentHeaderArgs) (returnAddress : Z) (call17_result : NextUint64Return) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt04a8_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (fp_machineAt04b0_ForwardA0N0_Hist (args) (returnAddress) (call17_result) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (⌜((bool_decide ((bv_zero_extend 64%N (bv_concat 16%N (List.nth 9%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z)) (List.nth 8%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z)))) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_concat 16%N (List.nth 9%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z)) (List.nth 8%nat ((nextResultBytes (call17_result))) (BV 8%N 0%Z)))) = (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt04a8_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt04b0_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_a84be01a9be85bdb, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_cbcac9df79b9221c.
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
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HN0.
Qed.

End edges.
