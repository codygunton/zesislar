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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0300Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0300Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0308Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0308Structural.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeObligations.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0300_ForwardA0N0 -> fp_machineAt026c_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_77 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0300_ForwardA0N0_Hist (args) (returnAddress) (call11_after) (call11_kept_x18) (call11_kept_x19) (call10_after) (call10_kept_x20) (call_after))
    (fp_machineAt026c_ForwardA0N0_Hist (args) (returnAddress) (call10_after) (call_after))
    (⌜(bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args)⌝ ∗ ⌜((bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((List.length call_after = 40)%nat)⌝ ∗ ⌜((List.length call10_after = 40)%nat)⌝ ∗ ⌜((List.length call11_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call11_kept_x19 (bv_sub call10_kept_x20 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call10_after (BV 8%N 0%Z)) (List.nth 30%nat call10_after (BV 8%N 0%Z))) (List.nth 29%nat call10_after (BV 8%N 0%Z))) (List.nth 28%nat call10_after (BV 8%N 0%Z))) (List.nth 27%nat call10_after (BV 8%N 0%Z))) (List.nth 26%nat call10_after (BV 8%N 0%Z))) (List.nth 25%nat call10_after (BV 8%N 0%Z))) (List.nth 24%nat call10_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((List.length call12_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call12_kept_x18 (bv_add call11_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call11_after (BV 8%N 0%Z)) (List.nth 30%nat call11_after (BV 8%N 0%Z))) (List.nth 29%nat call11_after (BV 8%N 0%Z))) (List.nth 28%nat call11_after (BV 8%N 0%Z))) (List.nth 27%nat call11_after (BV 8%N 0%Z))) (List.nth 26%nat call11_after (BV 8%N 0%Z))) (List.nth 25%nat call11_after (BV 8%N 0%Z))) (List.nth 24%nat call11_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call12_kept_x20 (bv_sub call11_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call11_after (BV 8%N 0%Z)) (List.nth 30%nat call11_after (BV 8%N 0%Z))) (List.nth 29%nat call11_after (BV 8%N 0%Z))) (List.nth 28%nat call11_after (BV 8%N 0%Z))) (List.nth 27%nat call11_after (BV 8%N 0%Z))) (List.nth 26%nat call11_after (BV 8%N 0%Z))) (List.nth 25%nat call11_after (BV 8%N 0%Z))) (List.nth 24%nat call11_after (BV 8%N 0%Z))))))⌝ ∗ ⌜(∃ (call12_arg_x14 : bv 64) (call12_arg_x15 : bv 64) (call12_arg_x16 : bv 64) (call12_arg_x17 : bv 64) (call12_arg_x13 : bv 64) (call12_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before) (call12_after)))⌝ ∗ ⌜(negb (bool_decide ((bv_zero_extend 64%N (bv_concat 16%N (List.nth 33%nat call12_after (BV 8%N 0%Z)) (List.nth 32%nat call12_after (BV 8%N 0%Z)))) = (BV 64%N 0%Z)))) = true⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. pose proof Hh as HS. unfold fp_machineAt0300_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_72b7e22ed74cb83b & forward_witness_87e5cadc5c04d5d4 & forward_witness_a84be01a9be85bdb & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24).
  iIntros "HN".
  iDestruct "HN" as "(%HV0 & %HV1 & %HV2 & %HV3 & %HV4 & %HV5 & %HV6 & %HV7 & %HV8 & %HV9 & %HG0 & _)".
  destruct HF1 as (call10_kept_x19_HF1 & call9_after_HF1 & call9_kept_x18_HF1 & call9_kept_x19_HF1 & call8_after_HF1 & call8_kept_x18_HF1 & call8_kept_x19_HF1 & call7_after_HF1 & call7_kept_x18_HF1 & call7_kept_x19_HF1 & call6_after_HF1 & call6_kept_x18_HF1 & call6_kept_x19_HF1 & call5_after_HF1 & call5_kept_x18_HF1 & call5_kept_x19_HF1 & call4_after_HF1 & call4_kept_x18_HF1 & call4_kept_x19_HF1 & call3_after_HF1 & call3_kept_x18_HF1 & call3_kept_x19_HF1 & call2_after_HF1 & call2_kept_x18_HF1 & call2_kept_x19_HF1 & HF1_0 & HF1_1 & HF1_2 & HF1_3 & HF1_4 & HF1_5 & HF1_6 & HF1_7 & HF1_8 & HF1_9 & HF1_10 & HF1_11 & HF1_12 & HF1_13 & HF1_14 & HF1_15 & HF1_16 & HF1_17 & HF1_18 & HF1_19 & HF1_20 & HF1_21 & HF1_22 & HF1_23 & HF1_24 & HF1_25 & HF1_26 & HF1_27 & HF1_28 & HF1_29 & HF1_30 & HF1_31 & HF1_32 & HF1_33 & HF1_34 & HF1_35 & HF1_36 & HF1_37 & HF1_38 & HF1_39 & HF1_40 & HF1_41 & HF1_42 & HF1_43 & HF1_44).
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt026c_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_9644ccf41f39915a.
  split; [exact HF0|].
  split; [exact (ex_intro _ call11_after (ex_intro _ call11_kept_x18 (ex_intro _ call11_kept_x19 (ex_intro _ call10_kept_x19_HF1 (ex_intro _ call10_kept_x20 (ex_intro _ call9_after_HF1 (ex_intro _ call9_kept_x18_HF1 (ex_intro _ call9_kept_x19_HF1 (ex_intro _ call8_after_HF1 (ex_intro _ call8_kept_x18_HF1 (ex_intro _ call8_kept_x19_HF1 (ex_intro _ call7_after_HF1 (ex_intro _ call7_kept_x18_HF1 (ex_intro _ call7_kept_x19_HF1 (ex_intro _ call6_after_HF1 (ex_intro _ call6_kept_x18_HF1 (ex_intro _ call6_kept_x19_HF1 (ex_intro _ call5_after_HF1 (ex_intro _ call5_kept_x18_HF1 (ex_intro _ call5_kept_x19_HF1 (ex_intro _ call4_after_HF1 (ex_intro _ call4_kept_x18_HF1 (ex_intro _ call4_kept_x19_HF1 (ex_intro _ call3_after_HF1 (ex_intro _ call3_kept_x18_HF1 (ex_intro _ call3_kept_x19_HF1 (ex_intro _ call2_after_HF1 (ex_intro _ call2_kept_x18_HF1 (ex_intro _ call2_kept_x19_HF1 (conj HF1_0 (conj HF1_1 (conj HF1_2 (conj HF1_3 (conj HF1_4 (conj HF1_5 (conj HF1_6 (conj HF1_7 (conj HF1_8 (conj HF1_9 (conj HF1_10 (conj HF1_11 (conj HF1_12 (conj HF1_13 (conj HF1_14 (conj HF1_15 (conj HF1_16 (conj HF1_17 (conj HF1_18 (conj HF1_19 (conj HF1_20 (conj HF1_21 (conj HF1_22 (conj HF1_23 (conj HF1_24 (conj HF1_25 (conj HF1_26 (conj HF1_27 (conj HF1_28 (conj HF1_29 (conj HF1_30 (conj HF1_31 (conj HF1_32 (conj HF1_33 (conj HF1_34 (conj HF1_35 (conj HF1_36 (conj HF1_37 (conj HF1_38 (conj HF1_39 (conj HF1_40 (conj HF1_41 (conj HF1_42 (conj HF1_43 (conj HV4 (conj HF1_44 (conj HV5 (conj HF2 HF3)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))|].
  split; [exact (fp_edge0300_026c_CandidateError_holds args returnAddress call12_after call12_kept_x18 call12_kept_x20 call11_after call11_kept_x18 call11_kept_x19 call10_after call10_kept_x20 call_after HS HV0 HV1 HV2 HV3 HV4 HV5 HV6 HV7 HV8 HV9 HG0)|].
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
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0300_ForwardA0N0 -> fp_machineAt0308_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_78 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0300_ForwardA0N0_Hist (args) (returnAddress) (call11_after) (call11_kept_x18) (call11_kept_x19) (call10_after) (call10_kept_x20) (call_after))
    (fp_machineAt0308_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_kept_x19) (call10_after) (call_after) (machine_x21_1))
    (⌜((bool_decide ((bv_zero_extend 64%N (bv_concat 16%N (List.nth 33%nat call12_after (BV 8%N 0%Z)) (List.nth 32%nat call12_after (BV 8%N 0%Z)))) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_concat 16%N (List.nth 33%nat call12_after (BV 8%N 0%Z)) (List.nth 32%nat call12_after (BV 8%N 0%Z)))) = (0%Z))%Z))⌝ ∗ ⌜((List.length call11_after = 40)%nat)⌝ ∗ ⌜((zesu_named_eq call11_kept_x19 (bv_sub call10_kept_x20 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call10_after (BV 8%N 0%Z)) (List.nth 30%nat call10_after (BV 8%N 0%Z))) (List.nth 29%nat call10_after (BV 8%N 0%Z))) (List.nth 28%nat call10_after (BV 8%N 0%Z))) (List.nth 27%nat call10_after (BV 8%N 0%Z))) (List.nth 26%nat call10_after (BV 8%N 0%Z))) (List.nth 25%nat call10_after (BV 8%N 0%Z))) (List.nth 24%nat call10_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call12_kept_x18 (bv_add call11_kept_x18 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call11_after (BV 8%N 0%Z)) (List.nth 30%nat call11_after (BV 8%N 0%Z))) (List.nth 29%nat call11_after (BV 8%N 0%Z))) (List.nth 28%nat call11_after (BV 8%N 0%Z))) (List.nth 27%nat call11_after (BV 8%N 0%Z))) (List.nth 26%nat call11_after (BV 8%N 0%Z))) (List.nth 25%nat call11_after (BV 8%N 0%Z))) (List.nth 24%nat call11_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call12_kept_x20 (bv_sub call11_kept_x19 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call11_after (BV 8%N 0%Z)) (List.nth 30%nat call11_after (BV 8%N 0%Z))) (List.nth 29%nat call11_after (BV 8%N 0%Z))) (List.nth 28%nat call11_after (BV 8%N 0%Z))) (List.nth 27%nat call11_after (BV 8%N 0%Z))) (List.nth 26%nat call11_after (BV 8%N 0%Z))) (List.nth 25%nat call11_after (BV 8%N 0%Z))) (List.nth 24%nat call11_after (BV 8%N 0%Z))))))⌝ ∗ ⌜(∃ (call12_arg_x14 : bv 64) (call12_arg_x15 : bv 64) (call12_arg_x16 : bv 64) (call12_arg_x17 : bv 64) (call12_arg_x13 : bv 64) (call12_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before) (call12_after)))⌝ ∗ ⌜((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call12_kept_x18) /\ bv_unsigned (call12_kept_x18) + bv_unsigned (call12_kept_x20) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z)⌝ ∗ ⌜(bv_unsigned machine_x21_1 = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold (parentHeaderInputBytes args) (Z.to_nat (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call11_after (BV 8%N 0%Z)) (List.nth 6%nat call11_after (BV 8%N 0%Z))) (List.nth 5%nat call11_after (BV 8%N 0%Z))) (List.nth 4%nat call11_after (BV 8%N 0%Z))) (List.nth 3%nat call11_after (BV 8%N 0%Z))) (List.nth 2%nat call11_after (BV 8%N 0%Z))) (List.nth 1%nat call11_after (BV 8%N 0%Z))) (List.nth 0%nat call11_after (BV 8%N 0%Z))) - bv_unsigned (parentHeaderInputPointer args))) (Z.to_nat (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call11_after (BV 8%N 0%Z)) (List.nth 14%nat call11_after (BV 8%N 0%Z))) (List.nth 13%nat call11_after (BV 8%N 0%Z))) (List.nth 12%nat call11_after (BV 8%N 0%Z))) (List.nth 11%nat call11_after (BV 8%N 0%Z))) (List.nth 10%nat call11_after (BV 8%N 0%Z))) (List.nth 9%nat call11_after (BV 8%N 0%Z))) (List.nth 8%nat call11_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((negb (bool_decide ((bv_signed (BV 128%N 8%Z) < bv_signed (bv_zero_extend 128%N (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call11_after (BV 8%N 0%Z)) (List.nth 14%nat call11_after (BV 8%N 0%Z))) (List.nth 13%nat call11_after (BV 8%N 0%Z))) (List.nth 12%nat call11_after (BV 8%N 0%Z))) (List.nth 11%nat call11_after (BV 8%N 0%Z))) (List.nth 10%nat call11_after (BV 8%N 0%Z))) (List.nth 9%nat call11_after (BV 8%N 0%Z))) (List.nth 8%nat call11_after (BV 8%N 0%Z)))))%Z))) = true) /\ ((((8%Z) >= (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call11_after (BV 8%N 0%Z)) (List.nth 14%nat call11_after (BV 8%N 0%Z))) (List.nth 13%nat call11_after (BV 8%N 0%Z))) (List.nth 12%nat call11_after (BV 8%N 0%Z))) (List.nth 11%nat call11_after (BV 8%N 0%Z))) (List.nth 10%nat call11_after (BV 8%N 0%Z))) (List.nth 9%nat call11_after (BV 8%N 0%Z))) (List.nth 8%nat call11_after (BV 8%N 0%Z)))))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0300_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_72b7e22ed74cb83b & forward_witness_87e5cadc5c04d5d4 & forward_witness_a84be01a9be85bdb & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV4 & %HV5 & %HV7 & %HV8 & %HV9 & %HV10 & %HV11 & %HV12 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0308_ForwardA0N0_Hist.
  exists call11_after, call11_kept_x18, call10_kept_x20, (BV 64%N 0%Z), forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_9644ccf41f39915a, forward_witness_87e5cadc5c04d5d4, forward_witness_a84be01a9be85bdb.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HV4|].
  split; [exact HV5|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HV7|].
  split; [exact HV8|].
  split; [exact HV9|].
  split; [exact HV10|].
  split; [exact HV11|].
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
  split; [exact HV12|].
  split; [by vm_compute|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [by vm_compute|].
  exact HN0.
Qed.

End edges.
