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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a0Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt048c_ForwardA0N0 -> fp_machineAt04a0_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_69 (args : TxAccessListArgs) (returnAddress : Z) (machine_x21 : bv 64) (call_after : DecodeItemOutcome) (tx_final : ArrayListState) (tx_final_done : list AccessListEntryValue) (tx_final_images : list TxAccessListEntryImage) (tx_final_rest : list byte) (call2_outcome : ToOwnedSliceOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt048c_ForwardA0N0_Hist (args) (returnAddress) (machine_x21) (call_after) (tx_final) (tx_final_done) (tx_final_images) (tx_final_rest))
    (fp_machineAt04a0_ForwardA0N0_Hist (args) (returnAddress) (call2_outcome) (machine_x21) (call_after) (tx_final) (tx_final_done) (tx_final_images) (tx_final_rest))
    (⌜(∃ (call2_arg_x13 : bv 64) (call2_arg_x14_1 : bv 64) (call2_arg_x15_1 : bv 64) (call2_arg_x16_1 : bv 64) (call2_arg_x17 : bv 64) (call2_arg_tx_final_scratch : list byte) (call2_context : Z) (call2_resultBefore : list byte), (entriesToOwnedSliceCallDomain ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551480%Z))); ((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551168%Z))); ((txAllocatorPointer args)); (call2_arg_x13); (call2_arg_x14_1); (call2_arg_x15_1); (call2_arg_x16_1); (call2_arg_x17)]) call2_context (tx_final) call2_resultBefore (call2_arg_tx_final_scratch)) /\ (entriesToOwnedSliceCallAllows (tx_final) call2_resultBefore (call2_outcome)))⌝ ∗ ⌜(∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before) (call_after)))⌝ ∗ ⌜((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z)) /\ ((((0%Z) <= (bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))))%Z)) /\ ((((bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))) <= (255%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt048c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_791c5acc1109e8e6 & forward_witness_88383840afa7af74 & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV3 & %HV6 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt04a0_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_791c5acc1109e8e6, forward_witness_88383840afa7af74, forward_witness_d77b5950a2aea933, (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HV3|].
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HN0|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HV6|].
  split; [exact HF12|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HF11.
Qed.

End edges.
