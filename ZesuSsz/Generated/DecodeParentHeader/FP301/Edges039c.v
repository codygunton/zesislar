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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot039cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot039cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt039c_LoopClass0 -> fp_machineAt03b0_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_92 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt039c_LoopClass0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call10_after) (call_after))
    (fp_machineAt03b0_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call10_after) (call_after))
    (⌜(List.length call12_after = 40)%nat⌝ ∗ ⌜∃ (call13_arg_x14 : bv 64) (call13_arg_x15 : bv 64) (call13_arg_x16 : bv 64) (call13_arg_x17 : bv 64) (call13_arg_x13 : bv 64) (call13_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call13_kept_x19); (call13_kept_x18); (call13_arg_x13); (call13_arg_x14); (call13_arg_x15); (call13_arg_x16); (call13_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call13_kept_x18))) (drop (Z.to_nat (bv_unsigned (call13_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call13_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call13_kept_x19); (call13_kept_x18); (call13_arg_x13); (call13_arg_x14); (call13_arg_x15); (call13_arg_x16); (call13_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call13_kept_x18))) (drop (Z.to_nat (bv_unsigned (call13_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call13_before) (call13_after))⌝ ∗ ⌜(bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call13_kept_x19) /\ bv_unsigned (call13_kept_x19) + bv_unsigned (call13_kept_x18) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt039c_LoopClass0_Hist in Hh.
  destruct Hh as (call12_kept_x20 & call11_kept_x19 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14).
  iIntros "HN".
  iDestruct "HN" as "(%HV4 & %HV6 & %HV7 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt03b0_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact (ex_intro _ call12_after (ex_intro _ call12_kept_x18 (ex_intro _ call12_kept_x20 (ex_intro _ call11_kept_x19 (conj HF1 (conj HV4 (conj HF2 (conj HF3 (conj HF4 HF5)))))))))|].
  split; [exact HV6|].
  split; [exact HV7|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF6|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF7|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF8|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF9|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF12|].
  zesu_hist_view HF13.
Qed.

End edges.
