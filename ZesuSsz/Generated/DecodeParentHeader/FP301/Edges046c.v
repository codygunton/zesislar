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
Require Import ZesuSsz.Contracts.ParentHeaderWalkFact.
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot046cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot046cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot048cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot048cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0498Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0498Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt046c_ForwardA0N0 -> fp_machineAt048c_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_117 (args : ParentHeaderArgs) (returnAddress : Z) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt046c_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (fp_machineAt048c_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call13_after) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (⌜((bool_decide (call16_kept_x18 = (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z))))) = true) /\ ((((bv_unsigned call16_kept_x18) = (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))%Z))⌝ ∗ ⌜((List.length call14_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call13_after (BV 8%N 0%Z)) (List.nth 30%nat call13_after (BV 8%N 0%Z))) (List.nth 29%nat call13_after (BV 8%N 0%Z))) (List.nth 28%nat call13_after (BV 8%N 0%Z))) (List.nth 27%nat call13_after (BV 8%N 0%Z))) (List.nth 26%nat call13_after (BV 8%N 0%Z))) (List.nth 25%nat call13_after (BV 8%N 0%Z))) (List.nth 24%nat call13_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call13_after (BV 8%N 0%Z)) (List.nth 30%nat call13_after (BV 8%N 0%Z))) (List.nth 29%nat call13_after (BV 8%N 0%Z))) (List.nth 28%nat call13_after (BV 8%N 0%Z))) (List.nth 27%nat call13_after (BV 8%N 0%Z))) (List.nth 26%nat call13_after (BV 8%N 0%Z))) (List.nth 25%nat call13_after (BV 8%N 0%Z))) (List.nth 24%nat call13_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((List.length call15_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call14_after (BV 8%N 0%Z)) (List.nth 30%nat call14_after (BV 8%N 0%Z))) (List.nth 29%nat call14_after (BV 8%N 0%Z))) (List.nth 28%nat call14_after (BV 8%N 0%Z))) (List.nth 27%nat call14_after (BV 8%N 0%Z))) (List.nth 26%nat call14_after (BV 8%N 0%Z))) (List.nth 25%nat call14_after (BV 8%N 0%Z))) (List.nth 24%nat call14_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call14_after (BV 8%N 0%Z)) (List.nth 30%nat call14_after (BV 8%N 0%Z))) (List.nth 29%nat call14_after (BV 8%N 0%Z))) (List.nth 28%nat call14_after (BV 8%N 0%Z))) (List.nth 27%nat call14_after (BV 8%N 0%Z))) (List.nth 26%nat call14_after (BV 8%N 0%Z))) (List.nth 25%nat call14_after (BV 8%N 0%Z))) (List.nth 24%nat call14_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call15_after (BV 8%N 0%Z)) (List.nth 30%nat call15_after (BV 8%N 0%Z))) (List.nth 29%nat call15_after (BV 8%N 0%Z))) (List.nth 28%nat call15_after (BV 8%N 0%Z))) (List.nth 27%nat call15_after (BV 8%N 0%Z))) (List.nth 26%nat call15_after (BV 8%N 0%Z))) (List.nth 25%nat call15_after (BV 8%N 0%Z))) (List.nth 24%nat call15_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call15_after (BV 8%N 0%Z)) (List.nth 30%nat call15_after (BV 8%N 0%Z))) (List.nth 29%nat call15_after (BV 8%N 0%Z))) (List.nth 28%nat call15_after (BV 8%N 0%Z))) (List.nth 27%nat call15_after (BV 8%N 0%Z))) (List.nth 26%nat call15_after (BV 8%N 0%Z))) (List.nth 25%nat call15_after (BV 8%N 0%Z))) (List.nth 24%nat call15_after (BV 8%N 0%Z))))))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt046c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV5 & %HV6 & %HV7 & %HV9 & %HV10 & %HV11 & %HV13 & %HV14 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt048c_ForwardA0N0_Hist.
  exists call15_after, call15_kept_x18, call15_kept_x19, call14_after, call14_kept_x18, call14_kept_x19, call13_kept_x18, call13_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_a84be01a9be85bdb, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HV5|].
  split; [exact HV6|].
  split; [exact HV7|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HV9|].
  split; [exact HV10|].
  split; [exact HV11|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HV13|].
  split; [exact HV14|].
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
  split; [exact HF35|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
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
  split; [exact HF36|].
  split; [exact HF37|].
  exact HN0.
Qed.

(* fp_machineAt046c_ForwardA0N0 -> fp_machineAt0498_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_118 (args : ParentHeaderArgs) (returnAddress : Z) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt046c_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (fp_machineAt0498_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (⌜((negb (bool_decide (call16_kept_x18 = (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))) = true) /\ ((((bv_unsigned call16_kept_x18) <> (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call16_after (BV 8%N 0%Z)) (List.nth 30%nat call16_after (BV 8%N 0%Z))) (List.nth 29%nat call16_after (BV 8%N 0%Z))) (List.nth 28%nat call16_after (BV 8%N 0%Z))) (List.nth 27%nat call16_after (BV 8%N 0%Z))) (List.nth 26%nat call16_after (BV 8%N 0%Z))) (List.nth 25%nat call16_after (BV 8%N 0%Z))) (List.nth 24%nat call16_after (BV 8%N 0%Z)))))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt046c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0498_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_a84be01a9be85bdb, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF35|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
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
  split; [exact HF36|].
  split; [exact HF37|].
  exact HN0.
Qed.

Global Instance zesu_hist_reveal_44 (args : ParentHeaderArgs) (returnAddress : Z) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) :
  ZesuHistReveal (fp_machineAt046c_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1)) ((∃ (call16_arg_x13 : bv 64) (call16_arg_x14 : bv 64) (call16_arg_x15 : bv 64) (call16_arg_x16 : bv 64) (call16_arg_x17 : bv 64) (call16_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551320%Z))); (call16_kept_x19); (call16_kept_x18); (call16_arg_x13); (call16_arg_x14); (call16_arg_x15); (call16_arg_x16); (call16_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call16_kept_x18))) (drop (Z.to_nat (bv_unsigned (call16_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call16_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551320%Z))); (call16_kept_x19); (call16_kept_x18); (call16_arg_x13); (call16_arg_x14); (call16_arg_x15); (call16_arg_x16); (call16_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call16_kept_x18))) (drop (Z.to_nat (bv_unsigned (call16_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call16_before) (call16_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt046c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37).
  exact HF9.
Qed.

Global Instance zesu_hist_reveal_45 (args : ParentHeaderArgs) (returnAddress : Z) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) :
  ZesuHistReveal (fp_machineAt046c_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call15_after) (call15_kept_x18) (call15_kept_x19) (call14_after) (call14_kept_x18) (call14_kept_x19) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after) (machine_x21_1) (machine_x22_1)) (((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call16_kept_x19) /\ bv_unsigned (call16_kept_x19) + bv_unsigned (call16_kept_x18) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt046c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37).
  exact HF10.
Qed.

End edges.
