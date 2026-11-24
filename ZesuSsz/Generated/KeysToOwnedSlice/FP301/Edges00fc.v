(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Export ZesuSsz.Compliance.KeysToOwnedSliceHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0110Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0148Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0148Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt00fc_ForwardA0N0 -> fp_machineAt0110_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_17 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (machine_x10 : bv 64) (machine_x23 : bv 64) (machine_x10_succ : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt00fc_ForwardA0N0_Hist (args) (returnAddress) (machine_x10) (machine_x23))
    (fp_machineAt0110_ForwardA0N0_Hist (args) (returnAddress) (machine_x10_succ))
    (⌜((bool_decide ((bv_unsigned machine_x10_succ >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10_succ <= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) <= (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt00fc_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0110_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_88383840afa7af74, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF1|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HN0|].
  split; [exact HN1|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt00fc_ForwardA0N0 -> fp_machineAt0148_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_18 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (machine_x10 : bv 64) (machine_x23 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt00fc_ForwardA0N0_Hist (args) (returnAddress) (machine_x10) (machine_x23))
    (fp_machineAt0148_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt00fc_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0148_ForwardA0N0_Hist.
  exists machine_x10, machine_x23, (BV 64%N 0%Z), forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_88383840afa7af74, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [by vm_compute|].
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
  split; [by vm_compute|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

End edges.
