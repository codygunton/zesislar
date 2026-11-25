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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0448Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot048cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0448_ForwardA0N0 -> fp_machineAt00c4_LoopClass0 (loop_back) *)
Global Instance zesu_hist_edge_67 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable))
    (fp_machineAt00c4_LoopClass0_Hist (args) (returnAddress) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00c4_LoopClass0_Hist.
  split; [exact (proj1 HF27)|].
  split; [exact (proj1 HF28)|].
  exact (proj1 HF29).
Qed.

Global Instance zesu_hist_reveal_36 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before) (call_after))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact HF0.
Qed.

Global Instance zesu_hist_reveal_37 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (arrayListLength tx_entries = Z.of_nat (length tx_done)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact HF1.
Qed.

Global Instance zesu_hist_reveal_38 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (arrayListItems tx_entries = txAccessListEntriesBytes tx_done tx_images).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact HF2.
Qed.

Global Instance zesu_hist_reveal_39 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (Forall (fun image => Z.of_nat (length (imagePadding image)) = txAccessListPaddingSize) tx_images).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact HF3.
Qed.

(* fp_machineAt0448_ForwardA0N0 -> fp_machineAt048c_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_68 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) (machine_x21 : bv 64) (tx_final : ArrayListState) (tx_final_done : list AccessListEntryValue) (tx_final_images : list TxAccessListEntryImage) (tx_final_rest : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable))
    (fp_machineAt048c_ForwardA0N0_Hist (args) (returnAddress) (machine_x21) (call_after) (tx_final) (tx_final_done) (tx_final_images) (tx_final_rest))
    (⌜((0%Z <= bv_unsigned machine_x21 <= 0%Z)%Z)⌝ ∗ ⌜(arrayListLength tx_final = Z.of_nat (List.length tx_final_done))⌝ ∗ ⌜(arrayListItems tx_final = txAccessListEntriesBytes tx_final_done tx_final_images)⌝ ∗ ⌜(Forall (fun image => Z.of_nat (List.length (imagePadding image)) = txAccessListPaddingSize) tx_final_images)⌝ ∗ ⌜(∃ (header_length payload_length : Z), candidateDecodeItem (txInputBytes args) = candidateSuccess true header_length payload_length /\ txAccessListOuterWalked (txInputBytes args) (header_length + payload_length) tx_final_done /\ tx_final_rest = app (word64Bytes (bv_unsigned (txInputPointer args) + (header_length + payload_length))) (word64Bytes (bv_unsigned (txInputLength args) - (header_length + payload_length))))⌝ ∗ ⌜((bool_decide (machine_x21 = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned machine_x21) = (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x21 >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x21) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x21 <= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x21) <= (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HN3 & %HN4 & %HN5 & %HN6 & %HN7 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt048c_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_791c5acc1109e8e6, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HN0|].
  split; [exact HN1|].
  split; [exact HN2|].
  split; [exact HN3|].
  split; [exact HN4|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [exact HF25|].
  split; [exact HF26|].
  split; [exact HF27|].
  split; [exact HF62|].
  split; [exact HF61|].
  split; [exact HF63|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [exact HN5|].
  split; [exact HN6|].
  exact HN7.
Qed.

Global Instance zesu_hist_reveal_40 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) ((∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before) (call_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact HF0.
Qed.

Global Instance zesu_hist_reveal_41 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z)) /\ ((((0%Z) <= (bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))))%Z)) /\ ((((bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))) <= (255%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact HF28.
Qed.

Global Instance zesu_hist_reveal_42 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (((negb (bool_decide ((bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z)) = (BV 64%N 0%Z)))) = true)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact (proj1 HF28).
Qed.

Global Instance zesu_hist_reveal_43 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (((((bv_unsigned (bv_and (bv_zero_extend 64%N (List.nth 16%nat call_after (BV 8%N 0%Z))) (BV 64%N 1%Z))) <> (0%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact (proj1 (proj2 HF28)).
Qed.

Global Instance zesu_hist_reveal_44 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (((((0%Z) <= (bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact (proj1 (proj2 (proj2 HF28))).
Qed.

Global Instance zesu_hist_reveal_45 (args : TxAccessListArgs) (returnAddress : Z) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_appendable : ArrayListState) :
  ZesuHistReveal (fp_machineAt0448_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (call3_kept_x26) (call5_outcome) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_appendable)) (((((bv_unsigned (List.nth 16%nat call_after (BV 8%N 0%Z))) <= (255%Z))%Z))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0448_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_done & tx_keys_list & tx_scratch_keys & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63).
  exact (proj2 (proj2 (proj2 HF28))).
Qed.

End edges.
