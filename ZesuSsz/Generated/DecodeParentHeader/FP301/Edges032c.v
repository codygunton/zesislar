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
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot032cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot032cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0334Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0334Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt032c_ForwardA0N0 -> fp_machineAt0334_LoopClass0 (loop_entry) *)
Global Instance zesu_hist_edge_78 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_after : DecodeItemOutcome) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt032c_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_after) (call11_kept_x19) (call10_after) (call_after))
    (fp_machineAt0334_LoopClass0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_after) (call11_kept_x19) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt032c_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x18 & call10_kept_x20 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0334_LoopClass0_Hist.
  exists call11_kept_x18, call10_kept_x20.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact (proj1 HF14)|].
  split; [exact (proj1 HF17)|].
  split; [exact (proj1 HF19)|].
  split; [exact (proj1 HF23)|].
  split; [exact (proj1 HF24)|].
  split; [exact (proj1 HF25)|].
  split; [exact (proj1 HF28)|].
  split; [exact (proj1 HF29)|].
  exact (proj1 HF30).
Qed.

Global Instance zesu_hist_reveal_38 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_after : DecodeItemOutcome) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt032c_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_after) (call11_kept_x19) (call10_after) (call_after)) (∃ (call12_arg_x14 : bv 64) (call12_arg_x15 : bv 64) (call12_arg_x16 : bv 64) (call12_arg_x17 : bv 64) (call12_arg_x13 : bv 64) (call12_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call12_kept_x18); (call12_kept_x20); (call12_arg_x13); (call12_arg_x14); (call12_arg_x15); (call12_arg_x16); (call12_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call12_kept_x20))) (drop (Z.to_nat (bv_unsigned (call12_kept_x18) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call12_before) (call12_after))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt032c_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x18 & call10_kept_x20 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  exact HF7.
Qed.

Global Instance zesu_hist_reveal_39 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_after : DecodeItemOutcome) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt032c_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_after) (call11_kept_x19) (call10_after) (call_after)) ((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call12_kept_x18) /\ bv_unsigned (call12_kept_x18) + bv_unsigned (call12_kept_x20) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt032c_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x18 & call10_kept_x20 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  exact HF8.
Qed.

Global Instance zesu_hist_reveal_40 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_after : DecodeItemOutcome) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt032c_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_after) (call11_kept_x19) (call10_after) (call_after)) ((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call12_kept_x18))%Z).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt032c_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x18 & call10_kept_x20 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  exact (proj1 HF8).
Qed.

Global Instance zesu_hist_reveal_41 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_after : DecodeItemOutcome) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt032c_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_after) (call11_kept_x19) (call10_after) (call_after)) ((bv_unsigned (call12_kept_x18) + bv_unsigned (call12_kept_x20) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt032c_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x18 & call10_kept_x20 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30).
  exact (proj2 HF8).
Qed.

End edges.
