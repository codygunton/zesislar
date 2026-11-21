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
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Contracts.ParentHeaderWalkFact.
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0334Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0334Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0348Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0348Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0334_LoopClass0 -> fp_machineAt0348_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_87 (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0334_LoopClass0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call12_kept_x20) (call11_kept_x19) (call10_after) (call_after) (machine_x21_1))
    (fp_machineAt0348_ForwardA0N0_Hist (args) (returnAddress) (call12_after) (call12_kept_x18) (call11_kept_x19) (call12_kept_x20) (machine_x21_1) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0334_LoopClass0_Hist in Hh.
  destruct Hh as (call11_after & call11_kept_x18 & call10_kept_x20 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0348_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact (ex_intro _ call11_after (ex_intro _ call11_kept_x18 (ex_intro _ call10_kept_x20 (conj HF1 (conj HF3 (conj HF4 (conj HF5 (conj HF6 (conj HF7 (conj HF8 HF9))))))))))|].
  split; [exact HF2|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF10|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF11|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF12|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF13|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF17|].
  zesu_hist_view HF18.
Qed.

End edges.
