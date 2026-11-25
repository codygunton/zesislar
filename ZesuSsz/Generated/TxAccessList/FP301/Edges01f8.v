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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01f8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot01f8Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0204Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0204Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt01f8_ForwardA0N0 -> fp_machineAt0204_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_36 (args : TxAccessListArgs) (returnAddress : Z) (call6_x10 : bv 64) (call6_outcome : EnsureCapacityOutcome) (call6_kept_x25 : bv 64) (call5_after : DecodeItemOutcome) (call5_payload_offset : Z) (call4_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) (inner_x22 : bv 64) (inner_x23 : bv 64) (inner_x24 : bv 64) (tx_keys : ArrayListState) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt01f8_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (call6_outcome) (call5_after) (call5_payload_offset) (call4_after) (outer_x20) (outer_x21) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_scratch) (inner_x22) (inner_x23) (inner_x24) (tx_keys))
    (fp_machineAt0204_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (call6_outcome) (call6_kept_x25) (call5_after) (call5_payload_offset) (call4_after) (outer_x20) (outer_x21) (call3_kept_x26) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_scratch) (inner_x22) (inner_x23) (inner_x24) (tx_keys))
    (⌜((bool_decide ((bv_shiftr (bv_shiftl call6_x10 (BV 64%N 48%Z)) (BV 64%N 48%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_shiftr (bv_shiftl call6_x10 (BV 64%N 48%Z)) (BV 64%N 48%Z))) = (0%Z))%Z))⌝ ∗ ⌜((zesu_named_eq call3_kept_x26 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call2_after (BV 8%N 0%Z)) (List.nth 30%nat call2_after (BV 8%N 0%Z))) (List.nth 29%nat call2_after (BV 8%N 0%Z))) (List.nth 28%nat call2_after (BV 8%N 0%Z))) (List.nth 27%nat call2_after (BV 8%N 0%Z))) (List.nth 26%nat call2_after (BV 8%N 0%Z))) (List.nth 25%nat call2_after (BV 8%N 0%Z))) (List.nth 24%nat call2_after (BV 8%N 0%Z)))))⌝ ∗ ⌜((zesu_named_eq call6_kept_x25 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call5_after (BV 8%N 0%Z)) (List.nth 30%nat call5_after (BV 8%N 0%Z))) (List.nth 29%nat call5_after (BV 8%N 0%Z))) (List.nth 28%nat call5_after (BV 8%N 0%Z))) (List.nth 27%nat call5_after (BV 8%N 0%Z))) (List.nth 26%nat call5_after (BV 8%N 0%Z))) (List.nth 25%nat call5_after (BV 8%N 0%Z))) (List.nth 24%nat call5_after (BV 8%N 0%Z)))))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt01f8_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_21649d1cf161453f & forward_witness_00470b017f14ddbf & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75 & HF76 & HF77 & HF78 & HF79 & HF80 & HF81 & HF82 & HF83 & HF84 & HF85 & HF86 & HF87 & HF88 & HF89 & HF90 & HF91 & HF92 & HF93 & HF94 & HF95 & HF96 & HF97).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV7 & %HV14 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0204_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_f1505c797ad3010d, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, forward_witness_21649d1cf161453f, forward_witness_00470b017f14ddbf, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HV7|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HV14|].
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
  split; [exact HF35|].
  split; [exact HF36|].
  split; [exact HF37|].
  split; [exact HF38|].
  split; [exact HF39|].
  split; [exact HF40|].
  split; [exact HF41|].
  split; [exact HF42|].
  split; [exact HF43|].
  split; [exact HF44|].
  split; [exact HF45|].
  split; [exact HF46|].
  split; [exact HF47|].
  split; [exact HF48|].
  split; [exact HF49|].
  split; [exact HF50|].
  split; [exact HF51|].
  split; [exact HF52|].
  split; [exact HF53|].
  split; [exact HF54|].
  split; [exact HF55|].
  split; [exact HF56|].
  split; [exact HF57|].
  split; [exact HF58|].
  split; [exact HF59|].
  split; [exact HF60|].
  split; [exact HF61|].
  split; [exact HF62|].
  split; [exact HF63|].
  split; [exact HF64|].
  split; [exact HF65|].
  split; [exact HF66|].
  split; [exact HF67|].
  split; [exact HF68|].
  split; [exact HF69|].
  split; [exact HF70|].
  split; [exact HF71|].
  split; [exact HF72|].
  split; [exact HF73|].
  split; [exact HF74|].
  split; [exact HF75|].
  split; [exact HF76|].
  split; [exact HF77|].
  split; [exact HF78|].
  split; [exact HF79|].
  split; [exact HF80|].
  split; [exact HF81|].
  split; [exact HF82|].
  split; [exact HF83|].
  split; [exact HF84|].
  split; [exact HF85|].
  split; [exact HF86|].
  split; [exact HF87|].
  split; [exact HF88|].
  split; [exact HF89|].
  split; [exact HF90|].
  split; [exact HF91|].
  split; [exact HF92|].
  split; [exact HF93|].
  split; [exact HF94|].
  split; [exact HF95|].
  split; [exact HF96|].
  split; [exact HF97|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HN0.
Qed.

(* fp_machineAt01f8_ForwardA0N0 -> fp_machineAt04a8_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_37 (args : TxAccessListArgs) (returnAddress : Z) (call6_x10 : bv 64) (call6_outcome : EnsureCapacityOutcome) (call5_after : DecodeItemOutcome) (call5_payload_offset : Z) (call4_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) (inner_x22 : bv 64) (inner_x23 : bv 64) (inner_x24 : bv 64) (tx_keys : ArrayListState) (tx_rest_error : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt01f8_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (call6_outcome) (call5_after) (call5_payload_offset) (call4_after) (outer_x20) (outer_x21) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_scratch) (inner_x22) (inner_x23) (inner_x24) (tx_keys))
    (fp_machineAt04a8_ForwardA0N0_Hist (args) (returnAddress) (call_after) (tx_rest_error))
    (⌜(∃ (consumed : Z), tx_rest_error = app (word64Bytes (bv_unsigned (txInputPointer args) + consumed)) (word64Bytes (bv_unsigned (txInputLength args) - consumed)))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt01f8_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_21649d1cf161453f & forward_witness_00470b017f14ddbf & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75 & HF76 & HF77 & HF78 & HF79 & HF80 & HF81 & HF82 & HF83 & HF84 & HF85 & HF86 & HF87 & HF88 & HF89 & HF90 & HF91 & HF92 & HF93 & HF94 & HF95 & HF96 & HF97).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt04a8_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f.
  split; [exact HF0|].
  split; [exact HN0|].
  split; [exact HF97|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
  exact HF23.
Qed.

End edges.
