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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot013cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot013cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0144Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0144Structural.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeObligations.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt013c_ForwardA0N0 -> fp_machineAt00a8_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_24 (args : ParentHeaderArgs) (returnAddress : Z) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt013c_ForwardA0N0_Hist (args) (returnAddress) (call4_after) (call4_kept_x18) (call4_kept_x19) (call3_after) (call3_kept_x18) (call3_kept_x19) (call2_after) (call2_kept_x18) (call2_kept_x19) (call_after))
    (fp_machineAt00a8_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (⌜(bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args)⌝ ∗ ⌜((bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((zesu_named_eq call2_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call_after (BV 8%N 0%Z)) (List.nth 14%nat call_after (BV 8%N 0%Z))) (List.nth 13%nat call_after (BV 8%N 0%Z))) (List.nth 12%nat call_after (BV 8%N 0%Z))) (List.nth 11%nat call_after (BV 8%N 0%Z))) (List.nth 10%nat call_after (BV 8%N 0%Z))) (List.nth 9%nat call_after (BV 8%N 0%Z))) (List.nth 8%nat call_after (BV 8%N 0%Z)))))⌝ ∗ ⌜((zesu_named_eq call2_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call_after (BV 8%N 0%Z)) (List.nth 6%nat call_after (BV 8%N 0%Z))) (List.nth 5%nat call_after (BV 8%N 0%Z))) (List.nth 4%nat call_after (BV 8%N 0%Z))) (List.nth 3%nat call_after (BV 8%N 0%Z))) (List.nth 2%nat call_after (BV 8%N 0%Z))) (List.nth 1%nat call_after (BV 8%N 0%Z))) (List.nth 0%nat call_after (BV 8%N 0%Z)))))⌝ ∗ ⌜((zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call2_after (BV 8%N 0%Z)) (List.nth 30%nat call2_after (BV 8%N 0%Z))) (List.nth 29%nat call2_after (BV 8%N 0%Z))) (List.nth 28%nat call2_after (BV 8%N 0%Z))) (List.nth 27%nat call2_after (BV 8%N 0%Z))) (List.nth 26%nat call2_after (BV 8%N 0%Z))) (List.nth 25%nat call2_after (BV 8%N 0%Z))) (List.nth 24%nat call2_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call2_after (BV 8%N 0%Z)) (List.nth 30%nat call2_after (BV 8%N 0%Z))) (List.nth 29%nat call2_after (BV 8%N 0%Z))) (List.nth 28%nat call2_after (BV 8%N 0%Z))) (List.nth 27%nat call2_after (BV 8%N 0%Z))) (List.nth 26%nat call2_after (BV 8%N 0%Z))) (List.nth 25%nat call2_after (BV 8%N 0%Z))) (List.nth 24%nat call2_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call3_after (BV 8%N 0%Z)) (List.nth 30%nat call3_after (BV 8%N 0%Z))) (List.nth 29%nat call3_after (BV 8%N 0%Z))) (List.nth 28%nat call3_after (BV 8%N 0%Z))) (List.nth 27%nat call3_after (BV 8%N 0%Z))) (List.nth 26%nat call3_after (BV 8%N 0%Z))) (List.nth 25%nat call3_after (BV 8%N 0%Z))) (List.nth 24%nat call3_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call3_after (BV 8%N 0%Z)) (List.nth 30%nat call3_after (BV 8%N 0%Z))) (List.nth 29%nat call3_after (BV 8%N 0%Z))) (List.nth 28%nat call3_after (BV 8%N 0%Z))) (List.nth 27%nat call3_after (BV 8%N 0%Z))) (List.nth 26%nat call3_after (BV 8%N 0%Z))) (List.nth 25%nat call3_after (BV 8%N 0%Z))) (List.nth 24%nat call3_after (BV 8%N 0%Z))))))⌝ ∗ ⌜(bool_decide (call4_kept_x18 = (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call4_after (BV 8%N 0%Z)) (List.nth 30%nat call4_after (BV 8%N 0%Z))) (List.nth 29%nat call4_after (BV 8%N 0%Z))) (List.nth 28%nat call4_after (BV 8%N 0%Z))) (List.nth 27%nat call4_after (BV 8%N 0%Z))) (List.nth 26%nat call4_after (BV 8%N 0%Z))) (List.nth 25%nat call4_after (BV 8%N 0%Z))) (List.nth 24%nat call4_after (BV 8%N 0%Z))))) = true⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. pose proof Hh as HS. unfold fp_machineAt013c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  iIntros "HN".
  iDestruct "HN" as "(%HV0 & %HV1 & %HV4 & %HV5 & %HV7 & %HV8 & %HV10 & %HV11 & %HG0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00a8_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f.
  split; [exact HF0|].
  split; [exact (fp_edge013c_00a8_CandidateError_holds args returnAddress call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after HS HV0 HV1 HV4 HV5 HV7 HV8 HV10 HV11 HG0)|].
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
  split; [exact HF28|].
  exact HF29.
Qed.

(* fp_machineAt013c_ForwardA0N0 -> fp_machineAt0144_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_25 (args : ParentHeaderArgs) (returnAddress : Z) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt013c_ForwardA0N0_Hist (args) (returnAddress) (call4_after) (call4_kept_x18) (call4_kept_x19) (call3_after) (call3_kept_x18) (call3_kept_x19) (call2_after) (call2_kept_x18) (call2_kept_x19) (call_after))
    (fp_machineAt0144_ForwardA0N0_Hist (args) (returnAddress) (call4_after) (call4_kept_x18) (call3_after) (call3_kept_x18) (call3_kept_x19) (call2_after) (call2_kept_x18) (call2_kept_x19) (call_after))
    (⌜((negb (bool_decide (call4_kept_x18 = (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call4_after (BV 8%N 0%Z)) (List.nth 30%nat call4_after (BV 8%N 0%Z))) (List.nth 29%nat call4_after (BV 8%N 0%Z))) (List.nth 28%nat call4_after (BV 8%N 0%Z))) (List.nth 27%nat call4_after (BV 8%N 0%Z))) (List.nth 26%nat call4_after (BV 8%N 0%Z))) (List.nth 25%nat call4_after (BV 8%N 0%Z))) (List.nth 24%nat call4_after (BV 8%N 0%Z)))))) = true) /\ ((((bv_unsigned call4_kept_x18) <> (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call4_after (BV 8%N 0%Z)) (List.nth 30%nat call4_after (BV 8%N 0%Z))) (List.nth 29%nat call4_after (BV 8%N 0%Z))) (List.nth 28%nat call4_after (BV 8%N 0%Z))) (List.nth 27%nat call4_after (BV 8%N 0%Z))) (List.nth 26%nat call4_after (BV 8%N 0%Z))) (List.nth 25%nat call4_after (BV 8%N 0%Z))) (List.nth 24%nat call4_after (BV 8%N 0%Z)))))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt013c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0144_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_407fca3a6f90b8db, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_a84be01a9be85bdb, forward_witness_9644ccf41f39915a.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
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
  exact HN0.
Qed.

Global Instance zesu_hist_reveal_16 (args : ParentHeaderArgs) (returnAddress : Z) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt013c_ForwardA0N0_Hist (args) (returnAddress) (call4_after) (call4_kept_x18) (call4_kept_x19) (call3_after) (call3_kept_x18) (call3_kept_x19) (call2_after) (call2_kept_x18) (call2_kept_x19) (call_after)) ((∃ (call4_arg_x13 : bv 64) (call4_arg_x14 : bv 64) (call4_arg_x15 : bv 64) (call4_arg_x16 : bv 64) (call4_arg_x17 : bv 64) (call4_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); (call4_kept_x19); (call4_kept_x18); (call4_arg_x13); (call4_arg_x14); (call4_arg_x15); (call4_arg_x16); (call4_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call4_kept_x18))) (drop (Z.to_nat (bv_unsigned (call4_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call4_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551280%Z))); (call4_kept_x19); (call4_kept_x18); (call4_arg_x13); (call4_arg_x14); (call4_arg_x15); (call4_arg_x16); (call4_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call4_kept_x18))) (drop (Z.to_nat (bv_unsigned (call4_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call4_before) (call4_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt013c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  exact HF5.
Qed.

Global Instance zesu_hist_reveal_17 (args : ParentHeaderArgs) (returnAddress : Z) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt013c_ForwardA0N0_Hist (args) (returnAddress) (call4_after) (call4_kept_x18) (call4_kept_x19) (call3_after) (call3_kept_x18) (call3_kept_x19) (call2_after) (call2_kept_x18) (call2_kept_x19) (call_after)) (((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call4_kept_x19) /\ bv_unsigned (call4_kept_x19) + bv_unsigned (call4_kept_x18) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt013c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  exact HF6.
Qed.

End edges.
