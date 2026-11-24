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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot018cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot018cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0204Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0204Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0248Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0248Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0204_ForwardA0N0 -> fp_machineAt018c_LoopClass0 (loop_back) *)
Global Instance zesu_hist_edge_24 (args : TxAccessListArgs) (returnAddress : Z) (call6_x10 : bv 64) (call6_outcome : EnsureCapacityOutcome) (call6_kept_x25 : bv 64) (call5_after : DecodeItemOutcome) (call5_payload_offset : Z) (call4_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) (inner_x22 : bv 64) (inner_x23 : bv 64) (inner_x24 : bv 64) (tx_keys : ArrayListState) (call3_kept_x22 : bv 64) (call3_kept_x23 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0204_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (call6_outcome) (call6_kept_x25) (call5_after) (call5_payload_offset) (call4_after) (outer_x20) (outer_x21) (call3_kept_x26) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_scratch) (inner_x22) (inner_x23) (inner_x24) (tx_keys))
    (fp_machineAt018c_LoopClass0_Hist (args) (returnAddress) (call4_after) (call3_after) (call3_kept_x22) (call3_kept_x23) (call3_kept_x26) (call3_payload_offset) (call2_after) (call_after) (outer_x20) (outer_x21) (tx_entries) (tx_done) (tx_images) (tx_scratch))
    (∃ (call2_kept_x23 : bv 64), ⌜(zesu_named_eq call2_kept_x23 (bv_add (txInputPointer args) (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call_after (BV 8%N 0%Z)) (List.nth 30%nat call_after (BV 8%N 0%Z))) (List.nth 29%nat call_after (BV 8%N 0%Z))) (List.nth 28%nat call_after (BV 8%N 0%Z))) (List.nth 27%nat call_after (BV 8%N 0%Z))) (List.nth 26%nat call_after (BV 8%N 0%Z))) (List.nth 25%nat call_after (BV 8%N 0%Z))) (List.nth 24%nat call_after (BV 8%N 0%Z)))))⌝ ∗ ⌜(zesu_named_eq call3_kept_x22 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call2_after (BV 8%N 0%Z)) (List.nth 14%nat call2_after (BV 8%N 0%Z))) (List.nth 13%nat call2_after (BV 8%N 0%Z))) (List.nth 12%nat call2_after (BV 8%N 0%Z))) (List.nth 11%nat call2_after (BV 8%N 0%Z))) (List.nth 10%nat call2_after (BV 8%N 0%Z))) (List.nth 9%nat call2_after (BV 8%N 0%Z))) (List.nth 8%nat call2_after (BV 8%N 0%Z))))⌝ ∗ ⌜(zesu_named_eq call3_kept_x23 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call2_after (BV 8%N 0%Z)) (List.nth 6%nat call2_after (BV 8%N 0%Z))) (List.nth 5%nat call2_after (BV 8%N 0%Z))) (List.nth 4%nat call2_after (BV 8%N 0%Z))) (List.nth 3%nat call2_after (BV 8%N 0%Z))) (List.nth 2%nat call2_after (BV 8%N 0%Z))) (List.nth 1%nat call2_after (BV 8%N 0%Z))) (List.nth 0%nat call2_after (BV 8%N 0%Z))))⌝ ∗ ⌜∃ (call3_arg_x13 : bv 64) (call3_arg_x14 : bv 64) (call3_arg_x15 : bv 64) (call3_arg_x16 : bv 64) (call3_arg_x17 : bv 64) (call3_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551232%Z))); (call3_kept_x23); (call3_kept_x22); (call3_arg_x13); (call3_arg_x14); (call3_arg_x15); (call3_arg_x16); (call3_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (take (Z.to_nat (bv_unsigned (call3_kept_x22))) (drop (Z.to_nat (bv_unsigned (call3_kept_x23) - bv_unsigned (txInputPointer args))) (txInputBytes args))) call3_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551232%Z))); (call3_kept_x23); (call3_kept_x22); (call3_arg_x13); (call3_arg_x14); (call3_arg_x15); (call3_arg_x16); (call3_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (take (Z.to_nat (bv_unsigned (call3_kept_x22))) (drop (Z.to_nat (bv_unsigned (call3_kept_x23) - bv_unsigned (txInputPointer args))) (txInputBytes args))) call3_before) (call3_after))⌝ ∗ ⌜(bv_unsigned (txInputPointer args) <= bv_unsigned (call3_kept_x23) /\ bv_unsigned (call3_kept_x23) + bv_unsigned (call3_kept_x22) <= bv_unsigned (txInputPointer args) + Z.of_nat (List.length (txInputBytes args)))%Z⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0204_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_21649d1cf161453f & forward_witness_00470b017f14ddbf & forward_witness_72b7e22ed74cb83b & forward_witness_87e5cadc5c04d5d4 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75 & HF76 & HF77 & HF78 & HF79 & HF80 & HF81 & HF82 & HF83 & HF84 & HF85 & HF86 & HF87 & HF88 & HF89 & HF90 & HF91 & HF92 & HF93 & HF94 & HF95 & HF96 & HF97 & HF98 & HF99 & HF100 & HF101 & HF102 & HF103 & HF104).
  iIntros "HN".
  iDestruct "HN" as (call2_kept_x23) "(%HN0 & %HN1 & %HN2 & %HN3 & %HN4 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt018c_LoopClass0_Hist.
  exists call2_kept_x23.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HN0|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HN1|].
  split; [exact HN2|].
  split; [exact HF10|].
  split; [exact HN3|].
  split; [exact HN4|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact (proj1 HF29)|].
  split; [exact (proj1 HF32)|].
  split; [exact (proj1 HF33)|].
  split; [exact (proj1 HF36)|].
  split; [exact (proj1 HF37)|].
  split; [exact (proj1 HF38)|].
  split; [exact (proj1 HF39)|].
  split; [exact (proj1 HF40)|].
  split; [exact (proj1 HF61)|].
  split; [exact (proj1 HF62)|].
  exact (proj1 HF63).
Qed.

Global Instance zesu_hist_reveal_24 (args : TxAccessListArgs) (returnAddress : Z) (call6_x10 : bv 64) (call6_outcome : EnsureCapacityOutcome) (call6_kept_x25 : bv 64) (call5_after : DecodeItemOutcome) (call5_payload_offset : Z) (call4_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) (inner_x22 : bv 64) (inner_x23 : bv 64) (inner_x24 : bv 64) (tx_keys : ArrayListState) :
  ZesuHistReveal (fp_machineAt0204_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (call6_outcome) (call6_kept_x25) (call5_after) (call5_payload_offset) (call4_after) (outer_x20) (outer_x21) (call3_kept_x26) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_scratch) (inner_x22) (inner_x23) (inner_x24) (tx_keys)) (arrayListWellFormed keysElementBytes tx_keys).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0204_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_21649d1cf161453f & forward_witness_00470b017f14ddbf & forward_witness_72b7e22ed74cb83b & forward_witness_87e5cadc5c04d5d4 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75 & HF76 & HF77 & HF78 & HF79 & HF80 & HF81 & HF82 & HF83 & HF84 & HF85 & HF86 & HF87 & HF88 & HF89 & HF90 & HF91 & HF92 & HF93 & HF94 & HF95 & HF96 & HF97 & HF98 & HF99 & HF100 & HF101 & HF102 & HF103 & HF104).
  exact HF13.
Qed.

(* fp_machineAt0204_ForwardA0N0 -> fp_machineAt0248_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_25 (args : TxAccessListArgs) (returnAddress : Z) (call6_x10 : bv 64) (call6_outcome : EnsureCapacityOutcome) (call6_kept_x25 : bv 64) (call5_after : DecodeItemOutcome) (call5_payload_offset : Z) (call4_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) (inner_x22 : bv 64) (inner_x23 : bv 64) (inner_x24 : bv 64) (tx_keys : ArrayListState) (machine_x22 : bv 64) (tx_keys_done : ArrayListState) (tx_scratch_keys : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0204_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (call6_outcome) (call6_kept_x25) (call5_after) (call5_payload_offset) (call4_after) (outer_x20) (outer_x21) (call3_kept_x26) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_scratch) (inner_x22) (inner_x23) (inner_x24) (tx_keys))
    (fp_machineAt0248_ForwardA0N0_Hist (args) (returnAddress) (outer_x20) (outer_x21) (machine_x22) (call3_kept_x26) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_keys_done) (tx_scratch_keys))
    (∃ (tx_keys_list : list (list byte)), ⌜((0%Z <= bv_unsigned machine_x22 <= 0%Z)%Z)⌝ ∗ ⌜(arrayListWellFormed keysElementBytes tx_keys_done)⌝ ∗ ⌜(arrayListItems tx_keys_done = concat tx_keys_list)⌝ ∗ ⌜(arrayListLength tx_keys_done = Z.of_nat (length tx_keys_list))⌝ ∗ ⌜(∃ keys_pointer keys_length, firstn 16 call4_after = word64Bytes keys_pointer ++ word64Bytes keys_length /\ txAccessListKeysWalked (take (Z.to_nat keys_length) (drop (Z.to_nat (keys_pointer - bv_unsigned (txInputPointer args))) (txInputBytes args))) keys_length tx_keys_list)⌝ ∗ ⌜(Z.of_nat (length tx_scratch_keys) = txAccessListScratchSize)⌝ ∗ ⌜((bool_decide (machine_x22 = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned machine_x22) = (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x22 >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x22) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x22 <= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x22) <= (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0204_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_21649d1cf161453f & forward_witness_00470b017f14ddbf & forward_witness_72b7e22ed74cb83b & forward_witness_87e5cadc5c04d5d4 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75 & HF76 & HF77 & HF78 & HF79 & HF80 & HF81 & HF82 & HF83 & HF84 & HF85 & HF86 & HF87 & HF88 & HF89 & HF90 & HF91 & HF92 & HF93 & HF94 & HF95 & HF96 & HF97 & HF98 & HF99 & HF100 & HF101 & HF102 & HF103 & HF104).
  iIntros "HN".
  iDestruct "HN" as (tx_keys_list) "(%HN0 & %HN1 & %HN2 & %HN3 & %HN4 & %HN5 & %HN6 & %HN7 & %HN8 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0248_ForwardA0N0_Hist.
  exists tx_scratch, tx_keys_list, (BV 64%N 0%Z), forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_88383840afa7af74, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, (BV 64%N 0%Z).
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
  split; [exact HN1|].
  split; [exact HN2|].
  split; [exact HN3|].
  split; [exact HN4|].
  split; [exact HN5|].
  split; [by vm_compute|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [exact HF25|].
  split; [exact HF26|].
  split; [exact HF27|].
  split; [exact HF28|].
  split; [exact HF29|].
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
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [exact HN6|].
  split; [exact HN7|].
  exact HN8.
Qed.

End edges.
