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
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0000Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0000Structural.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0044Entries.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot0044Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0000_ForwardA0N0 -> fp_machineAt0044_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_0 (args : NextUint64Args) (returnAddress : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0000_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt0044_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0000_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & HF0).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0044_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HF0.
Qed.

End edges.
