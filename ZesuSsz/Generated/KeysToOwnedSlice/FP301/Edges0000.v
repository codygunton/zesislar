(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
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
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0000Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0000Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0058Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0058Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0078Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0078Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0000_ForwardA0N0 -> fp_machineAt0058_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_0 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0000_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt0058_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0000_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & HF0).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0058_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0000_ForwardA0N0 -> fp_machineAt0078_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_1 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0000_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt0078_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0000_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & HF0).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0078_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

End edges.
