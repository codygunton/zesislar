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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0274Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0274Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0270_ForwardA0N0 -> fp_machineAt0274_slot0_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_58 (args : ParentHeaderArgs) (returnAddress : Z) (machine_x10 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0270_ForwardA0N0_Hist (args) (returnAddress) (machine_x10) (call10_after) (call_after))
    (fp_machineAt0274_slot0_ForwardA0N0_Hist (args) (returnAddress) (call10_after) (call_after) (machine_x10))
    (∃ (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_kept_x19 : bv 64) (call10_kept_x20 : bv 64) (call9_after : DecodeItemOutcome) (call9_kept_x18 : bv 64) (call9_kept_x19 : bv 64) (call8_after : DecodeItemOutcome) (call8_kept_x18 : bv 64) (call8_kept_x19 : bv 64) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64), True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0270_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_d77b5950a2aea933 & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18).
  iIntros "HN".
  iDestruct "HN" as (call11_after call11_kept_x18 call11_kept_x19 call10_kept_x19 call10_kept_x20 call9_after call9_kept_x18 call9_kept_x19 call8_after call8_kept_x18 call8_kept_x19 call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19) "_".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0274_slot0_ForwardA0N0_Hist.
  exists call11_after, call11_kept_x18, call11_kept_x19, call10_kept_x19, call10_kept_x20, call9_after, call9_kept_x18, call9_kept_x19, call8_after, call8_kept_x18, call8_kept_x19, call7_after, call7_kept_x18, call7_kept_x19, call6_after, call6_kept_x18, call6_kept_x19, call5_after, call5_kept_x18, call5_kept_x19, call4_after, call4_kept_x18, call4_kept_x19, call3_after, call3_kept_x18, call3_kept_x19, call2_after, call2_kept_x18, call2_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff.
  split; [exact HF0|].
  split; [exact HF1|].
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
  exact HF18.
Qed.

End edges.
