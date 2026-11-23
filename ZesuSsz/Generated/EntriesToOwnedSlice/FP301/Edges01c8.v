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
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Export ZesuSsz.Compliance.EntriesToOwnedSliceHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01c8Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01f0Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot01f0Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt01c8_ForwardA0N0 -> fp_machineAt01f0_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_30 (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (call_x10 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt01c8_ForwardA0N0_Hist (args) (returnAddress) (call_x10))
    (fp_machineAt01f0_ForwardA0N0_Hist (args) (returnAddress) (call_x10))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt01c8_ForwardA0N0_Hist in Hh.
  destruct Hh as (machine_x10 & machine_x23 & fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_a84be01a9be85bdb & forward_witness_21649d1cf161453f & forward_witness_9644ccf41f39915a & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_11fde2df72db9d06 & forward_witness_d77b5950a2aea933 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt01f0_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_a84be01a9be85bdb, forward_witness_21649d1cf161453f, forward_witness_9644ccf41f39915a, forward_witness_407fca3a6f90b8db, forward_witness_1eea82d2945b4618, forward_witness_11fde2df72db9d06, forward_witness_d77b5950a2aea933.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF21|].
  split; [exact HF22|].
  exact HF20.
Qed.

End edges.
