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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0188Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0188Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot018cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot018cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0188_ForwardA0N0 -> fp_machineAt018c_LoopClass0 (loop_entry) *)
Global Instance zesu_hist_edge_16 (args : TxAccessListArgs) (returnAddress : Z) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_kept_x22 : bv 64) (call3_kept_x23 : bv 64) (call3_kept_x26 : bv 64) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0188_ForwardA0N0_Hist (args) (returnAddress) (call4_after) (call3_after) (call3_kept_x22) (call3_kept_x23) (call3_kept_x26) (call3_payload_offset) (call2_after) (call_after) (outer_x20) (outer_x21) (tx_entries) (tx_done) (tx_images) (tx_scratch))
    (fp_machineAt018c_LoopClass0_Hist (args) (returnAddress) (call4_after) (call3_after) (call3_kept_x22) (call3_kept_x23) (call3_kept_x26) (call3_payload_offset) (call2_after) (call_after) (outer_x20) (outer_x21) (tx_entries) (tx_done) (tx_images) (tx_scratch))
    (⌜((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call4_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call4_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z)) /\ ((((0%Z) <= (bv_unsigned (List.nth 16%nat call4_after (BV 8%N 0%Z))))%Z)) /\ ((((bv_unsigned (List.nth 16%nat call4_after (BV 8%N 0%Z))) <= (255%Z))%Z))⌝ ∗ ⌜((negb (bool_decide ((bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call4_after (BV 8%N 0%Z)) (List.nth 14%nat call4_after (BV 8%N 0%Z))) (List.nth 13%nat call4_after (BV 8%N 0%Z))) (List.nth 12%nat call4_after (BV 8%N 0%Z))) (List.nth 11%nat call4_after (BV 8%N 0%Z))) (List.nth 10%nat call4_after (BV 8%N 0%Z))) (List.nth 9%nat call4_after (BV 8%N 0%Z))) (List.nth 8%nat call4_after (BV 8%N 0%Z))) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call4_after (BV 8%N 0%Z)) (List.nth 14%nat call4_after (BV 8%N 0%Z))) (List.nth 13%nat call4_after (BV 8%N 0%Z))) (List.nth 12%nat call4_after (BV 8%N 0%Z))) (List.nth 11%nat call4_after (BV 8%N 0%Z))) (List.nth 10%nat call4_after (BV 8%N 0%Z))) (List.nth 9%nat call4_after (BV 8%N 0%Z))) (List.nth 8%nat call4_after (BV 8%N 0%Z)))) <> (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0188_ForwardA0N0_Hist in Hh.
  destruct Hh as (call2_kept_x23 & fp_seed_mstatus_bits & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_1be931110d776902 & forward_witness_751588b52f8a71ff & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61).
  iIntros "HN".
  iDestruct "HN" as "(%HV7 & %HV8 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt018c_LoopClass0_Hist.
  exists call2_kept_x23.
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
  split; [exact (proj1 HF25)|].
  split; [exact (proj1 HF28)|].
  split; [exact (proj1 HF29)|].
  split; [exact (proj1 HF32)|].
  split; [exact (proj1 HF33)|].
  split; [exact (proj1 HF35)|].
  split; [exact (proj1 HF36)|].
  split; [exact (proj1 HF38)|].
  split; [exact (proj1 HF60)|].
  split; [exact (proj1 HV7)|].
  exact (proj1 HV8).
Qed.

End edges.
