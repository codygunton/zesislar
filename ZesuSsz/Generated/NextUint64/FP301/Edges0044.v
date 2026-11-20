(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Export ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0044Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0044Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot004cEntries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot004cStructural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0064Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0064Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0044_ForwardA0N0 -> fp_machineAt004c_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_1 (args : NextUint64Args) (returnAddress : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0044_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt004c_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0044_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_9644ccf41f39915a & forward_witness_407fca3a6f90b8db & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt004c_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_9644ccf41f39915a, forward_witness_407fca3a6f90b8db, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_791c5acc1109e8e6, (BV 64%N 0%Z).
  split; [by vm_compute|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0044_ForwardA0N0 -> fp_machineAt0064_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_2 (args : NextUint64Args) (returnAddress : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0044_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt0064_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0044_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_9644ccf41f39915a & forward_witness_407fca3a6f90b8db & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0064_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_9644ccf41f39915a, forward_witness_407fca3a6f90b8db, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_791c5acc1109e8e6, (BV 64%N 0%Z).
  split; [by vm_compute|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

End edges.
