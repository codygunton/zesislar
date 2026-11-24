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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00c4Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00c4Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00d8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot00d8Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt00c4_LoopClass0 -> fp_machineAt00d8_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_8 (args : TxAccessListArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) (call2_after : DecodeItemOutcome) (outer_x20_succ : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt00c4_LoopClass0_Hist (args) (returnAddress) (call_after))
    (fp_machineAt00d8_ForwardA0N0_Hist (args) (returnAddress) (call2_after) (call_after) (outer_x20_succ) (tx_entries) (tx_done) (tx_images) (tx_scratch))
    (⌜(txAccessListOuterWalked (txInputBytes args) (bv_unsigned outer_x20_succ - bv_unsigned (txInputPointer args)) tx_done)⌝ ∗ ⌜(bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 call2_after (BV 8 0))) (BV 64 1)) <> 0 -> (bv_unsigned (txInputPointer args) <= bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (@take (bv 8) (N.to_nat 8) (@drop (bv 8) 0 call2_after)))))%Z /\ (bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (@take (bv 8) (N.to_nat 8) (@drop (bv 8) 0 call2_after)))) + bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (@take (bv 8) (N.to_nat 8) (@drop (bv 8) 8 call2_after)))) <= bv_unsigned (txInputPointer args) + Z.of_nat (length (txInputBytes args)))%Z)⌝ ∗ ⌜∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before) (call_after))⌝ ∗ ⌜arrayListLength tx_entries = Z.of_nat (length tx_done)⌝ ∗ ⌜arrayListItems tx_entries = txAccessListEntriesBytes tx_done tx_images⌝ ∗ ⌜Forall (fun image => Z.of_nat (length (imagePadding image)) = txAccessListPaddingSize) tx_images⌝ ∗ ⌜Z.of_nat (length tx_scratch) = txAccessListScratchSize⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt00c4_LoopClass0_Hist in Hh.
  destruct Hh as (HF0 & HF1 & HF2).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HV3 & %HV11 & %HV12 & %HV13 & %HV14 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00d8_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HV3|].
  split; [exact HV11|].
  split; [exact HV12|].
  split; [exact HV13|].
  split; [exact HV14|].
  split; [exact HN0|].
  split; [exact HN1|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF0|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF1|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF2|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

End edges.
