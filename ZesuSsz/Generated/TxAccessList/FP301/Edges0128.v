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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0128Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0128Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot015cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot015cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0128_ForwardA0N0 -> fp_machineAt015c_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_12 (args : TxAccessListArgs) (returnAddress : Z) (call3_after : DecodeItemOutcome) (call3_kept_x22 : bv 64) (call3_kept_x23 : bv 64) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_scratch : list byte) (call3_payload_offset_succ : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0128_ForwardA0N0_Hist (args) (returnAddress) (call3_after) (call2_after) (call_after) (outer_x20) (outer_x21) (tx_entries) (tx_done) (tx_images) (tx_scratch))
    (fp_machineAt015c_ForwardA0N0_Hist (args) (returnAddress) (call3_after) (call3_kept_x22) (call3_kept_x23) (call3_payload_offset_succ) (call2_after) (call_after) (outer_x20) (outer_x21) (tx_entries) (tx_done) (tx_images) (tx_scratch))
    (⌜((bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call3_after (BV 8%N 0%Z)) (List.nth 6%nat call3_after (BV 8%N 0%Z))) (List.nth 5%nat call3_after (BV 8%N 0%Z))) (List.nth 4%nat call3_after (BV 8%N 0%Z))) (List.nth 3%nat call3_after (BV 8%N 0%Z))) (List.nth 2%nat call3_after (BV 8%N 0%Z))) (List.nth 1%nat call3_after (BV 8%N 0%Z))) (List.nth 0%nat call3_after (BV 8%N 0%Z))) = bv_unsigned (txInputPointer args) + call3_payload_offset_succ)%Z)⌝ ∗ ⌜((1 <= call3_payload_offset_succ)%Z)⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 1%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 1%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 2%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 2%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 3%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 3%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 4%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 4%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 5%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 5%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 6%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 6%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 7%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 7%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 1%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 1%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 2%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 2%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 3%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 3%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 4%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 4%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 5%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 5%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 6%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 6%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 7%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 8%Z)) (BV 64%N 7%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (BV 64%N 1%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (BV 64%N 1%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (BV 64%N 2%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (BV 64%N 2%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (BV 64%N 3%Z)) (txInputPointer args)) < bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args))))))%Z)) = true) /\ ((((bv_unsigned (bv_sub (bv_add (bv_add (bv_add (txInputPointer args) ((Z_to_bv 64%N (call3_payload_offset_succ)))) (BV 64%N 16%Z)) (BV 64%N 3%Z)) (txInputPointer args))) < (bv_unsigned ((Z_to_bv 64%N (Z.of_nat (List.length (txInputBytes args)))))))%Z))⌝ ∗ ⌜(∃ (call3_arg_x13 : bv 64) (call3_arg_x14 : bv 64) (call3_arg_x15 : bv 64) (call3_arg_x16 : bv 64) (call3_arg_x17 : bv 64) (call3_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551232%Z))); (call3_kept_x23); (call3_kept_x22); (call3_arg_x13); (call3_arg_x14); (call3_arg_x15); (call3_arg_x16); (call3_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (take (Z.to_nat (bv_unsigned (call3_kept_x22))) (drop (Z.to_nat (bv_unsigned (call3_kept_x23) - bv_unsigned (txInputPointer args))) (txInputBytes args))) call3_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551232%Z))); (call3_kept_x23); (call3_kept_x22); (call3_arg_x13); (call3_arg_x14); (call3_arg_x15); (call3_arg_x16); (call3_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (take (Z.to_nat (bv_unsigned (call3_kept_x22))) (drop (Z.to_nat (bv_unsigned (call3_kept_x23) - bv_unsigned (txInputPointer args))) (txInputBytes args))) call3_before) (call3_after)))⌝ ∗ ⌜((bv_unsigned (txInputPointer args) <= bv_unsigned (call3_kept_x23) /\ bv_unsigned (call3_kept_x23) + bv_unsigned (call3_kept_x22) <= bv_unsigned (txInputPointer args) + Z.of_nat (List.length (txInputBytes args)))%Z)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0128_ForwardA0N0_Hist in Hh.
  destruct Hh as (call3_payload_offset & fp_seed_mstatus_bits & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_21649d1cf161453f & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HN3 & %HN4 & %HN5 & %HN6 & %HN7 & %HN8 & %HN9 & %HN10 & %HN11 & %HN12 & %HN13 & %HN14 & %HN15 & %HN16 & %HN17 & %HN18 & %HN19 & %HN20 & %HN21 & %HV9 & %HV10 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt015c_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_791c5acc1109e8e6, forward_witness_f1505c797ad3010d, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, forward_witness_1be931110d776902, forward_witness_21649d1cf161453f.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HV9|].
  split; [exact HV10|].
  split; [exact HN0|].
  split; [exact HN1|].
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
  split; [exact HF26|].
  split; [exact HF27|].
  split; [exact HF28|].
  split; [exact HF29|].
  split; [exact HF30|].
  split; [exact HF32|].
  split; [exact HF35|].
  split; [exact HF36|].
  split; [exact HF37|].
  split; [exact HF38|].
  split; [exact HN2|].
  split; [exact HN3|].
  split; [exact HN4|].
  split; [exact HN5|].
  split; [exact HN6|].
  split; [exact HN7|].
  split; [exact HN8|].
  split; [exact HN9|].
  split; [exact HN10|].
  split; [exact HN11|].
  split; [exact HN12|].
  split; [exact HN13|].
  split; [exact HN14|].
  split; [exact HN15|].
  split; [exact HN16|].
  split; [exact HN17|].
  split; [exact HN18|].
  split; [exact HN19|].
  split; [exact HN20|].
  split; [exact HN21|].
  exact HF33.
Qed.

End edges.
