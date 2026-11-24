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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0264Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0264Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02a0Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot02a0Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0264_ForwardA0N0 -> fp_machineAt02a0_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_43 (args : TxAccessListArgs) (returnAddress : Z) (call5_outcome : ToOwnedSliceOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (machine_x22 : bv 64) (call3_kept_x26 : bv 64) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_keys_done : ArrayListState) (tx_scratch_keys : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0264_ForwardA0N0_Hist (args) (returnAddress) (call5_outcome) (outer_x20) (outer_x21) (machine_x22) (call3_kept_x26) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_keys_done) (tx_scratch_keys))
    (fp_machineAt02a0_ForwardA0N0_Hist (args) (returnAddress) (call5_outcome) (outer_x20) (outer_x21) (machine_x22) (call3_kept_x26) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_keys_done) (tx_scratch_keys))
    (⌜((negb (bool_decide ((bv_signed (bv_zero_extend 128%N (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)) (List.nth 14%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 13%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 12%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 11%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 10%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 9%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 8%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)))) < bv_signed (bv_zero_extend 128%N (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 23%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)) (List.nth 22%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 21%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 20%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 19%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 18%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 17%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 16%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)))))%Z))) = true) /\ ((((bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)) (List.nth 14%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 13%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 12%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 11%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 10%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 9%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 8%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)))) >= (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 23%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)) (List.nth 22%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 21%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 20%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 19%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 18%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 17%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z))) (List.nth 16%nat (arrayListHeaderBytes tx_entries) (BV 8%N 0%Z)))))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0264_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_list & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_1be931110d776902 & forward_witness_87e5cadc5c04d5d4 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt02a0_ForwardA0N0_Hist.
  exists tx_scratch, tx_keys_list, fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_88383840afa7af74, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
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
  split; [exact HF61|].
  split; [exact HF58|].
  split; [exact HF59|].
  split; [exact HF60|].
  split; [exact HF65|].
  split; [exact HF66|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HN0.
Qed.

(* fp_machineAt0264_ForwardA0N0 -> fp_machineAt0448_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_44 (args : TxAccessListArgs) (returnAddress : Z) (call5_outcome : ToOwnedSliceOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (machine_x22 : bv 64) (call3_kept_x26 : bv 64) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_keys_done : ArrayListState) (tx_scratch_keys : list byte) (machine_x11 : bv 64) (machine_x12 : bv 64) (machine_x16 : bv 64) (tx_appendable : ArrayListState) (tx_scratch_append : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0264_ForwardA0N0_Hist (args) (returnAddress) (call5_outcome) (outer_x20) (outer_x21) (machine_x22) (call3_kept_x26) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_keys_done) (tx_scratch_keys))
    (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (machine_x11) (machine_x12) (machine_x16) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable) (tx_scratch_append))
    (⌜((40 <= (arrayListCapacity tx_appendable - arrayListLength tx_appendable) * entriesElementBytes)%Z)⌝ ∗ ⌜(bv_unsigned (machine_x11) = arrayListPointer tx_appendable)⌝ ∗ ⌜(arrayListLength tx_appendable = arrayListLength tx_entries)⌝ ∗ ⌜(arrayListItems tx_appendable = arrayListItems tx_entries)⌝ ∗ ⌜((arrayListLength tx_appendable < arrayListCapacity tx_appendable)%Z)⌝ ∗ ⌜((bv_unsigned (machine_x12) = 8 * arrayListLength tx_appendable)%Z)⌝ ∗ ⌜((bv_unsigned (machine_x16) = 32 * arrayListLength tx_appendable)%Z)⌝ ∗ ⌜(Z.of_nat (List.length tx_scratch_append) = txAccessListScratchSize)⌝ ∗ ⌜(arrayListWellFormed keysElementBytes tx_keys_done)⌝ ∗ ⌜((List.length ((if arrayListLength (tx_keys_done) =? 0 then (tx_scratch_keys)
           else match toOwnedKind (call5_outcome) with
                | arrayListSuccess => word64Bytes (arrayListLength (tx_keys_done) * keysElementBytes)
                | arrayListOutOfMemory => (tx_scratch_keys)
                end)%Z) = 8)%nat)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0264_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_list & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_1be931110d776902 & forward_witness_87e5cadc5c04d5d4 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HN3 & %HN4 & %HN5 & %HN6 & %HN7 & %HV7 & %HV10 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0448_ForwardA0N0_Hist.
  exists tx_scratch, tx_keys_done, tx_keys_list, tx_scratch_keys, fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
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
  split; [exact (ex_intro _ machine_x22 HF13)|].
  split; [exact HV7|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HV10|].
  split; [exact HF18|].
  split; [exact HN0|].
  split; [exact HN1|].
  split; [exact HN2|].
  split; [exact HN3|].
  split; [exact HN4|].
  split; [exact HN5|].
  split; [exact HN6|].
  split; [exact HN7|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [exact HF25|].
  split; [exact HF26|].
  split; [exact HF27|].
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
  split; [exact HF66|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [exact HF61|].
  exact HF65.
Qed.

End edges.
