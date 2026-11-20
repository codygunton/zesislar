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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot037cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot037cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0388Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0388Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt037c_ForwardA0N0 -> fp_machineAt026c_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_86 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt037c_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after))
    (fp_machineAt026c_ForwardA0N0_Hist (args) (returnAddress) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt037c_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29).
  iIntros "HN".
  destruct HF1 as (call11_after_HF1 & call11_kept_x18_HF1 & call10_kept_x20_HF1 & HF1_0 & HF1_1 & HF1_2 & HF1_3 & HF1_4 & HF1_5 & HF1_6).
  destruct HF1_0 as (call10_kept_x19_HF1_0 & call9_after_HF1_0 & call9_kept_x18_HF1_0 & call9_kept_x19_HF1_0 & call8_after_HF1_0 & call8_kept_x18_HF1_0 & call8_kept_x19_HF1_0 & call7_after_HF1_0 & call7_kept_x18_HF1_0 & call7_kept_x19_HF1_0 & call6_after_HF1_0 & call6_kept_x18_HF1_0 & call6_kept_x19_HF1_0 & call5_after_HF1_0 & call5_kept_x18_HF1_0 & call5_kept_x19_HF1_0 & call4_after_HF1_0 & call4_kept_x18_HF1_0 & call4_kept_x19_HF1_0 & call3_after_HF1_0 & call3_kept_x18_HF1_0 & call3_kept_x19_HF1_0 & call2_after_HF1_0 & call2_kept_x18_HF1_0 & call2_kept_x19_HF1_0 & HF1_0_0 & HF1_0_1 & HF1_0_2 & HF1_0_3 & HF1_0_4 & HF1_0_5 & HF1_0_6 & HF1_0_7 & HF1_0_8 & HF1_0_9 & HF1_0_10 & HF1_0_11 & HF1_0_12 & HF1_0_13 & HF1_0_14 & HF1_0_15 & HF1_0_16 & HF1_0_17 & HF1_0_18 & HF1_0_19 & HF1_0_20 & HF1_0_21 & HF1_0_22 & HF1_0_23 & HF1_0_24 & HF1_0_25 & HF1_0_26 & HF1_0_27 & HF1_0_28 & HF1_0_29 & HF1_0_30 & HF1_0_31 & HF1_0_32 & HF1_0_33 & HF1_0_34 & HF1_0_35 & HF1_0_36 & HF1_0_37 & HF1_0_38 & HF1_0_39 & HF1_0_40 & HF1_0_41 & HF1_0_42 & HF1_0_43 & HF1_0_44).
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt026c_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_9644ccf41f39915a.
  split; [exact HF0|].
  split; [exact (ex_intro _ call11_after_HF1 (ex_intro _ call11_kept_x18_HF1 (ex_intro _ call11_kept_x19 (ex_intro _ call10_kept_x19_HF1_0 (ex_intro _ call10_kept_x20_HF1 (ex_intro _ call9_after_HF1_0 (ex_intro _ call9_kept_x18_HF1_0 (ex_intro _ call9_kept_x19_HF1_0 (ex_intro _ call8_after_HF1_0 (ex_intro _ call8_kept_x18_HF1_0 (ex_intro _ call8_kept_x19_HF1_0 (ex_intro _ call7_after_HF1_0 (ex_intro _ call7_kept_x18_HF1_0 (ex_intro _ call7_kept_x19_HF1_0 (ex_intro _ call6_after_HF1_0 (ex_intro _ call6_kept_x18_HF1_0 (ex_intro _ call6_kept_x19_HF1_0 (ex_intro _ call5_after_HF1_0 (ex_intro _ call5_kept_x18_HF1_0 (ex_intro _ call5_kept_x19_HF1_0 (ex_intro _ call4_after_HF1_0 (ex_intro _ call4_kept_x18_HF1_0 (ex_intro _ call4_kept_x19_HF1_0 (ex_intro _ call3_after_HF1_0 (ex_intro _ call3_kept_x18_HF1_0 (ex_intro _ call3_kept_x19_HF1_0 (ex_intro _ call2_after_HF1_0 (ex_intro _ call2_kept_x18_HF1_0 (ex_intro _ call2_kept_x19_HF1_0 (conj HF1_0_0 (conj HF1_0_1 (conj HF1_0_2 (conj HF1_0_3 (conj HF1_0_4 (conj HF1_0_5 (conj HF1_0_6 (conj HF1_0_7 (conj HF1_0_8 (conj HF1_0_9 (conj HF1_0_10 (conj HF1_0_11 (conj HF1_0_12 (conj HF1_0_13 (conj HF1_0_14 (conj HF1_0_15 (conj HF1_0_16 (conj HF1_0_17 (conj HF1_0_18 (conj HF1_0_19 (conj HF1_0_20 (conj HF1_0_21 (conj HF1_0_22 (conj HF1_0_23 (conj HF1_0_24 (conj HF1_0_25 (conj HF1_0_26 (conj HF1_0_27 (conj HF1_0_28 (conj HF1_0_29 (conj HF1_0_30 (conj HF1_0_31 (conj HF1_0_32 (conj HF1_0_33 (conj HF1_0_34 (conj HF1_0_35 (conj HF1_0_36 (conj HF1_0_37 (conj HF1_0_38 (conj HF1_0_39 (conj HF1_0_40 (conj HF1_0_41 (conj HF1_0_42 (conj HF1_0_43 (conj HF1_1 (conj HF1_0_44 (conj HF1_2 (conj HF1_3 HF1_4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))|].
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
  split; [exact HF25|].
  exact HF27.
Qed.

(* fp_machineAt037c_ForwardA0N0 -> fp_machineAt0388_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_87 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt037c_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after))
    (fp_machineAt0388_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt037c_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0388_ForwardA0N0_Hist.
  exists call11_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_9644ccf41f39915a.
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
  split; [exact HF27|].
  split; [exact HF28|].
  exact HF29.
Qed.

End edges.
