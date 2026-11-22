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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0348Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0348Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0368Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0368Structural.
Require Import ZesuSsz.Compliance.ParentHeaderWalkObligations.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0348_ForwardA0N0 -> fp_machineAt0368_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_88 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call12_kept_x20 : bv 64) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0348_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call11_kept_x19) (call12_kept_x20) (machine_x21_1) (call10_after) (call_after))
    (fp_machineAt0368_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after) (machine_x21_1) (machine_x22_1))
    (⌜(bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args)⌝ ∗ ⌜((bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((List.length call12_after = 40)%nat)⌝ ∗ ⌜(∃ (call12_arg_x14 : bv 64) (call12_arg_x15 : bv 64) (call12_arg_x16 : bv 64) (call12_arg_x17 : bv 64) (call12_arg_x13 : bv 64) (call12_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before) (call12_after)))⌝ ∗ ⌜((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call12_kept_x18) /\ bv_unsigned (call12_kept_x18) + bv_unsigned (call12_kept_x20) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z)⌝ ∗ ⌜(bv_unsigned machine_x22_1 = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold (parentHeaderInputBytes args) (Z.to_nat (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call12_after (BV 8%N 0%Z)) (List.nth 6%nat call12_after (BV 8%N 0%Z))) (List.nth 5%nat call12_after (BV 8%N 0%Z))) (List.nth 4%nat call12_after (BV 8%N 0%Z))) (List.nth 3%nat call12_after (BV 8%N 0%Z))) (List.nth 2%nat call12_after (BV 8%N 0%Z))) (List.nth 1%nat call12_after (BV 8%N 0%Z))) (List.nth 0%nat call12_after (BV 8%N 0%Z))) - bv_unsigned (parentHeaderInputPointer args))) (Z.to_nat (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call12_after (BV 8%N 0%Z)) (List.nth 14%nat call12_after (BV 8%N 0%Z))) (List.nth 13%nat call12_after (BV 8%N 0%Z))) (List.nth 12%nat call12_after (BV 8%N 0%Z))) (List.nth 11%nat call12_after (BV 8%N 0%Z))) (List.nth 10%nat call12_after (BV 8%N 0%Z))) (List.nth 9%nat call12_after (BV 8%N 0%Z))) (List.nth 8%nat call12_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((negb (bool_decide ((bv_signed (BV 128%N 8%Z) < bv_signed (bv_zero_extend 128%N (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call12_after (BV 8%N 0%Z)) (List.nth 14%nat call12_after (BV 8%N 0%Z))) (List.nth 13%nat call12_after (BV 8%N 0%Z))) (List.nth 12%nat call12_after (BV 8%N 0%Z))) (List.nth 11%nat call12_after (BV 8%N 0%Z))) (List.nth 10%nat call12_after (BV 8%N 0%Z))) (List.nth 9%nat call12_after (BV 8%N 0%Z))) (List.nth 8%nat call12_after (BV 8%N 0%Z)))))%Z))) = true) /\ ((((8%Z) >= (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call12_after (BV 8%N 0%Z)) (List.nth 14%nat call12_after (BV 8%N 0%Z))) (List.nth 13%nat call12_after (BV 8%N 0%Z))) (List.nth 12%nat call12_after (BV 8%N 0%Z))) (List.nth 11%nat call12_after (BV 8%N 0%Z))) (List.nth 10%nat call12_after (BV 8%N 0%Z))) (List.nth 9%nat call12_after (BV 8%N 0%Z))) (List.nth 8%nat call12_after (BV 8%N 0%Z)))))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. pose proof Hh as HS. unfold fp_machineAt0348_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21).
  iIntros "HN".
  iDestruct "HN" as "(%HV0 & %HV1 & %HV4 & %HV5 & %HV6 & %HV7 & %HV8 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0368_ForwardA0N0_Hist.
  exists call11_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_9644ccf41f39915a, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HV5|].
  split; [exact HV6|].
  split; [exact (fp_edge0348_0368_Walk_holds args returnAddress call12_after call12_kept_x18 call11_kept_x19 call12_kept_x20 machine_x21_1 machine_x22_1 call10_after call_after HS HV0 HV1 HV4 HV5 HV7 HV8)|].
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
  split; [exact HF20|].
  split; [exact HF21|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HF18.
Qed.

End edges.
