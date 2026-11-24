(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Interfaces.KeysToOwnedSlice.
Require Export ZesuSsz.Interfaces.EntriesToOwnedSlice.
Require Export ZesuSsz.Interfaces.KeysEnsureCapacity.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Export ZesuSsz.Compliance.TxAccessListHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot007cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot007cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00acEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00acStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt007c_ForwardA0N0 -> fp_machineAt00ac_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_5 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (fp_machineAt00ac_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00ac_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_791c5acc1109e8e6, forward_witness_f1505c797ad3010d, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF1|].
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
  split; [by vm_compute|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

Global Instance zesu_hist_reveal_0 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after)) ((∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before) (call_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  exact HF0.
Qed.

Global Instance zesu_hist_reveal_1 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z)) /\ ((((0%Z) <= (bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))))%Z)) /\ ((((bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))) <= (255%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  exact HF17.
Qed.

Global Instance zesu_hist_reveal_2 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  exact (proj1 HF17).
Qed.

Global Instance zesu_hist_reveal_3 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  exact (proj1 (proj2 HF17)).
Qed.

Global Instance zesu_hist_reveal_4 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((((0%Z) <= (bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  exact (proj1 (proj2 (proj2 HF17))).
Qed.

Global Instance zesu_hist_reveal_5 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after)) (((((bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))) <= (255%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  exact (proj2 (proj2 (proj2 HF17))).
Qed.

(* fp_machineAt007c_ForwardA0N0 -> fp_machineAt048c_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_6 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) (machine_x21 : bv 64) (tx_final : ArrayListState) (tx_final_done : list AccessListEntryValue) (tx_final_images : list TxAccessListEntryImage) (tx_final_scratch : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt007c_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (fp_machineAt048c_ForwardA0N0_Hist (args) (returnAddress) (machine_x21) (call_after) (tx_final) (tx_final_done) (tx_final_images) (tx_final_scratch))
    (∃ (join_resource_31_bytes : list byte), ⌜((0%Z <= bv_unsigned machine_x21 <= 0%Z)%Z)⌝ ∗ ⌜((List.length join_resource_31_bytes = List.length (txBlockRestBytes args))%nat)⌝ ∗ ⌜(arrayListLength tx_final = Z.of_nat (List.length tx_final_done))⌝ ∗ ⌜(arrayListItems tx_final = txAccessListEntriesBytes tx_final_done tx_final_images)⌝ ∗ ⌜(Forall (fun image => Z.of_nat (List.length (imagePadding image)) = txAccessListPaddingSize) tx_final_images)⌝ ∗ ⌜(Z.of_nat (List.length tx_final_scratch) = txAccessListScratchSize)⌝ ∗ ⌜(∃ (header_length payload_length : Z), candidateDecodeItem (txInputBytes args) = candidateSuccess true header_length payload_length /\ txAccessListOuterWalked (txInputBytes args) (header_length + payload_length) tx_final_done)⌝ ∗ ⌜((bool_decide (machine_x21 = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned machine_x21) = (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x21 >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x21) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x21 <= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x21) <= (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt007c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  iIntros "HN".
  iDestruct "HN" as (join_resource_31_bytes) "(%HN0 & %HN1 & %HN2 & %HN3 & %HN4 & %HN5 & %HN6 & %HN7 & %HN8 & %HN9 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt048c_ForwardA0N0_Hist.
  exists join_resource_31_bytes, fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_791c5acc1109e8e6, forward_witness_88383840afa7af74, forward_witness_d77b5950a2aea933.
  split; [exact HN0|].
  split; [exact HN1|].
  split; [exact HN2|].
  split; [exact HN3|].
  split; [exact HN4|].
  split; [exact HN5|].
  split; [exact HN6|].
  split; [exact HF6|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF14|].
  split; [exact HF1|].
  split; [exact HF4|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF16|].
  split; [exact HN7|].
  split; [exact HN8|].
  exact HN9.
Qed.

End edges.
