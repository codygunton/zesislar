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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0274Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0274Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0274_slot0_ForwardA0N0 -> fp_machineReturn_slot0_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_59 (args : ParentHeaderArgs) (returnAddress : Z) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x10 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0274_slot0_ForwardA0N0_Hist (args) (returnAddress) (call10_after) (call_after) (machine_x10))
    (fp_machineReturn_slot0_ForwardA0N0_Hist (args) (returnAddress) (call10_after) (call_after) (machine_x10))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0274_slot0_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_after & call11_kept_x18 & call11_kept_x19 & call10_kept_x19 & call10_kept_x20 & call9_after & call9_kept_x18 & call9_kept_x19 & call8_after & call8_kept_x18 & call8_kept_x19 & call7_after & call7_kept_x18 & call7_kept_x19 & call6_after & call6_kept_x18 & call6_kept_x19 & call5_after & call5_kept_x18 & call5_kept_x19 & call4_after & call4_kept_x18 & call4_kept_x19 & call3_after & call3_kept_x18 & call3_kept_x19 & call2_after & call2_kept_x18 & call2_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot0_ForwardA0N0_Hist.
  exists call11_after, call11_kept_x18, call11_kept_x19, call10_kept_x19, call10_kept_x20, call9_after, call9_kept_x18, call9_kept_x19, call8_after, call8_kept_x18, call8_kept_x19, call7_after, call7_kept_x18, call7_kept_x19, call6_after, call6_kept_x18, call6_kept_x19, call5_after, call5_kept_x18, call5_kept_x19, call4_after, call4_kept_x18, call4_kept_x19, call3_after, call3_kept_x18, call3_kept_x19, call2_after, call2_kept_x18, call2_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF14|].
  split; [exact HF7|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF13|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  by vm_compute.
Qed.

(* fp_machineAt0274_slot1_ForwardA0N0 -> fp_machineReturn_slot1_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_60 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x10 : bv 64) (machine_x18 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0274_slot1_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call10_after) (call_after) (machine_x10) (machine_x18))
    (fp_machineReturn_slot1_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call10_after) (call_after) (machine_x10))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0274_slot1_ForwardA0N0_Hist in Hh.
  destruct Hh as (call13_kept_x18 & call13_kept_x19 & call12_after & call12_kept_x18 & call12_kept_x20 & call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_751588b52f8a71ff & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot1_ForwardA0N0_Hist.
  exists call13_kept_x18, call13_kept_x19, call12_after, call12_kept_x18, call12_kept_x20, call11_kept_x19, machine_x18, fp_seed_mstatus_bits, forward_witness_751588b52f8a71ff, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
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
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0274_slot2_ForwardA0N0 -> fp_machineReturn_slot2_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_61 (args : ParentHeaderArgs) (returnAddress : Z) (call19_result : NextUint64Return) (call19_word_1_0 : bv 64) (call19_word_1_8 : bv 64) (call19_kept_x19 : bv 64) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call16_after : DecodeItemOutcome) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0274_slot2_ForwardA0N0_Hist (args) (returnAddress) (call19_result) (call19_word_1_0) (call19_word_1_8) (call19_kept_x19) (call18_after) (call17_result) (call16_after) (call13_after) (call10_after) (call_after))
    (fp_machineReturn_slot2_ForwardA0N0_Hist (args) (returnAddress) (call19_result) (call19_word_1_0) (call19_word_1_8) (call18_after) (call17_result) (call16_after) (call13_after) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0274_slot2_ForwardA0N0_Hist in Hh.
  destruct Hh as (call17_word_1_0 & call17_word_1_8 & call17_kept_x19 & call16_kept_x18 & call16_kept_x19 & call15_after & call15_kept_x18 & call15_kept_x19 & call14_after & call14_kept_x18 & call14_kept_x19 & call13_kept_x18 & call13_kept_x19 & fp_seed_mstatus_bits & forward_witness_d77b5950a2aea933 & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_9644ccf41f39915a & forward_witness_184f6fc7524c683f & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot2_ForwardA0N0_Hist.
  exists call19_kept_x19, call17_word_1_0, call17_word_1_8, call17_kept_x19, call16_kept_x18, call16_kept_x19, call15_after, call15_kept_x18, call15_kept_x19, call14_after, call14_kept_x18, call14_kept_x19, call13_kept_x18, call13_kept_x19, fp_seed_mstatus_bits, forward_witness_d77b5950a2aea933, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_9644ccf41f39915a, forward_witness_184f6fc7524c683f, (BV 64%N 0%Z), (BV 64%N 0%Z).
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
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0274_slot3_ForwardA0N0 -> fp_machineReturn_slot3_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_62 (args : ParentHeaderArgs) (returnAddress : Z) (call20_result : NextUint64Return) (call20_word_1_0 : bv 64) (call20_word_1_8 : bv 64) (call19_result : NextUint64Return) (call19_kept_x19 : bv 64) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call16_after : DecodeItemOutcome) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0274_slot3_ForwardA0N0_Hist (args) (returnAddress) (call20_result) (call20_word_1_0) (call20_word_1_8) (call19_result) (call19_kept_x19) (call18_after) (call17_result) (call16_after) (call13_after) (call10_after) (call_after))
    (fp_machineReturn_slot3_ForwardA0N0_Hist (args) (returnAddress) (call20_result) (call20_word_1_0) (call20_word_1_8) (call19_result) (call18_after) (call17_result) (call16_after) (call13_after) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0274_slot3_ForwardA0N0_Hist in Hh.
  destruct Hh as (call19_word_1_0 & call19_word_1_8 & call17_word_1_0 & call17_word_1_8 & call17_kept_x19 & call16_kept_x18 & call16_kept_x19 & call15_after & call15_kept_x18 & call15_kept_x19 & call14_after & call14_kept_x18 & call14_kept_x19 & call13_kept_x18 & call13_kept_x19 & fp_seed_mstatus_bits & forward_witness_88383840afa7af74 & forward_witness_9644ccf41f39915a & forward_witness_1492ef7bd46b3b7a & forward_witness_21649d1cf161453f & forward_witness_dc636cab9ffb40ae & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot3_ForwardA0N0_Hist.
  exists call19_word_1_0, call19_word_1_8, call19_kept_x19, call17_word_1_0, call17_word_1_8, call17_kept_x19, call16_kept_x18, call16_kept_x19, call15_after, call15_kept_x18, call15_kept_x19, call14_after, call14_kept_x18, call14_kept_x19, call13_kept_x18, call13_kept_x19, fp_seed_mstatus_bits, forward_witness_88383840afa7af74, forward_witness_9644ccf41f39915a, forward_witness_1492ef7bd46b3b7a, forward_witness_21649d1cf161453f, forward_witness_dc636cab9ffb40ae, (BV 64%N 0%Z), (BV 64%N 0%Z).
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
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0274_slot4_ForwardA0N0 -> fp_machineReturn_slot4_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_63 (args : ParentHeaderArgs) (returnAddress : Z) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0274_slot4_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call13_after) (call10_after) (call_after))
    (fp_machineReturn_slot4_ForwardA0N0_Hist (args) (returnAddress) (call16_after) (call16_kept_x18) (call16_kept_x19) (call13_after) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0274_slot4_ForwardA0N0_Hist in Hh.
  destruct Hh as (call15_after & call15_kept_x18 & call15_kept_x19 & call14_after & call14_kept_x18 & call14_kept_x19 & call13_kept_x18 & call13_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_cbcac9df79b9221c & forward_witness_1b5321dec05d0d89 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot4_ForwardA0N0_Hist.
  exists call15_after, call15_kept_x18, call15_kept_x19, call14_after, call14_kept_x18, call14_kept_x19, call13_kept_x18, call13_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_a84be01a9be85bdb, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_cbcac9df79b9221c, forward_witness_1b5321dec05d0d89, (BV 64%N 0%Z), (BV 64%N 0%Z).
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
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0274_slot5_ForwardA0N0 -> fp_machineReturn_slot5_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_64 (args : ParentHeaderArgs) (returnAddress : Z) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call17_kept_x19 : bv 64) (call16_after : DecodeItemOutcome) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0274_slot5_ForwardA0N0_Hist (args) (returnAddress) (call17_result) (call17_word_1_0) (call17_word_1_8) (call17_kept_x19) (call16_after) (call13_after) (call10_after) (call_after))
    (fp_machineReturn_slot5_ForwardA0N0_Hist (args) (returnAddress) (call17_result) (call17_word_1_0) (call17_word_1_8) (call16_after) (call13_after) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0274_slot5_ForwardA0N0_Hist in Hh.
  destruct Hh as (call16_kept_x18 & call16_kept_x19 & call15_after & call15_kept_x18 & call15_kept_x19 & call14_after & call14_kept_x18 & call14_kept_x19 & call13_kept_x18 & call13_kept_x19 & fp_seed_mstatus_bits & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_9644ccf41f39915a & forward_witness_8da77898f656116a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot5_ForwardA0N0_Hist.
  exists call17_kept_x19, call16_kept_x18, call16_kept_x19, call15_after, call15_kept_x18, call15_kept_x19, call14_after, call14_kept_x18, call14_kept_x19, call13_kept_x18, call13_kept_x19, fp_seed_mstatus_bits, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_9644ccf41f39915a, forward_witness_8da77898f656116a, (BV 64%N 0%Z), (BV 64%N 0%Z).
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
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0274_slot6_ForwardA0N0 -> fp_machineReturn_slot6_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_65 (args : ParentHeaderArgs) (returnAddress : Z) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call16_after : DecodeItemOutcome) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0274_slot6_ForwardA0N0_Hist (args) (returnAddress) (call18_after) (call17_result) (call17_word_1_0) (call17_word_1_8) (call16_after) (call13_after) (call10_after) (call_after))
    (fp_machineReturn_slot6_ForwardA0N0_Hist (args) (returnAddress) (call18_after) (call17_result) (call17_word_1_0) (call17_word_1_8) (call16_after) (call13_after) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0274_slot6_ForwardA0N0_Hist in Hh.
  destruct Hh as (call17_kept_x19 & call16_kept_x18 & call16_kept_x19 & call15_after & call15_kept_x18 & call15_kept_x19 & call14_after & call14_kept_x18 & call14_kept_x19 & call13_kept_x18 & call13_kept_x19 & fp_seed_mstatus_bits & forward_witness_d77b5950a2aea933 & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & forward_witness_9644ccf41f39915a & forward_witness_1492ef7bd46b3b7a & forward_witness_184f6fc7524c683f & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot6_ForwardA0N0_Hist.
  exists call17_kept_x19, call16_kept_x18, call16_kept_x19, call15_after, call15_kept_x18, call15_kept_x19, call14_after, call14_kept_x18, call14_kept_x19, call13_kept_x18, call13_kept_x19, fp_seed_mstatus_bits, forward_witness_d77b5950a2aea933, forward_witness_407fca3a6f90b8db, forward_witness_88383840afa7af74, forward_witness_9644ccf41f39915a, forward_witness_1492ef7bd46b3b7a, forward_witness_184f6fc7524c683f, (BV 64%N 0%Z), (BV 64%N 0%Z).
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
  split; [by vm_compute|].
  by vm_compute.
Qed.

End edges.
