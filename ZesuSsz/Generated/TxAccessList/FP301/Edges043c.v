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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot043cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot043cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt043c_ForwardA0N0 -> fp_machineAt0448_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_49 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call6_x10 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_grown : ArrayListState) (machine_x12 : bv 64) (machine_x16 : bv 64) (tx_appendable : ArrayListState) (tx_scratch_append : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt043c_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call6_x10) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_grown))
    (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (machine_x12) (machine_x16) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable) (tx_scratch_append))
    (⌜(zesu_join_history (∃ (machine_x22 : bv 64), ((0%Z <= bv_unsigned machine_x22 <= 0%Z)%Z)))⌝ ∗ ⌜((40 <= (arrayListCapacity tx_appendable - arrayListLength tx_appendable) * entriesElementBytes)%Z)⌝ ∗ ⌜(bv_unsigned (call6_x10) = arrayListPointer tx_appendable)⌝ ∗ ⌜(arrayListLength tx_appendable = arrayListLength tx_entries)⌝ ∗ ⌜(arrayListItems tx_appendable = arrayListItems tx_entries)⌝ ∗ ⌜(arrayListLength tx_appendable < arrayListCapacity tx_appendable)⌝ ∗ ⌜(bv_unsigned (machine_x12) = 8 * arrayListLength tx_appendable)⌝ ∗ ⌜(bv_unsigned (machine_x16) = 32 * arrayListLength tx_appendable)⌝ ∗ ⌜(Z.of_nat (List.length tx_scratch_append) = txAccessListScratchSize)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt043c_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_00470b017f14ddbf & forward_witness_8da77898f656116a & forward_witness_eba071f2aafca867 & forward_witness_6b5c9f21ea2547d9 & forward_witness_1b5321dec05d0d89 & forward_witness_407fca3a6f90b8db & forward_witness_cbcac9df79b9221c & forward_witness_d77b5950a2aea933 & forward_witness_a84be01a9be85bdb & forward_witness_21649d1cf161453f & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75 & HF76 & HF77 & HF78 & HF79 & HF80 & HF81 & HF82 & HF83).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HN3 & %HN4 & %HN5 & %HN6 & %HN7 & %HN8 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0448_ForwardA0N0_Hist.
  exists tx_scratch, tx_keys_done, tx_keys_list, tx_scratch_keys, fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_791c5acc1109e8e6.
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
  split; [exact HN0|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HN1|].
  split; [exact HN2|].
  split; [exact HN3|].
  split; [exact HN4|].
  split; [exact HN5|].
  split; [exact HN6|].
  split; [exact HN7|].
  split; [exact HN8|].
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
  split; [exact HF75|].
  exact HF83.
Qed.

End edges.
