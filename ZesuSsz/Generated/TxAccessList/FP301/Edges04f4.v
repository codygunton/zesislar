(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Interfaces.KeysToOwnedSlice.
Require Export ZesuSsz.Interfaces.EntriesToOwnedSlice.
Require Export ZesuSsz.Interfaces.KeysEnsureCapacity.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Export ZesuSsz.Compliance.TxAccessListHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04b8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04b8Structural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04f4Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04f4Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt04f4_ForwardA0N0 -> fp_machineAt04b8_slot1_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_75 (args : TxAccessListArgs) (returnAddress : Z) (call2_outcome : ToOwnedSliceOutcome) (machine_x21 : bv 64) (call_after : DecodeItemOutcome) (tx_final : ArrayListState) (tx_final_done : list AccessListEntryValue) (tx_final_images : list TxAccessListEntryImage) (tx_final_rest : list byte) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt04f4_ForwardA0N0_Hist (args) (returnAddress) (call2_outcome) (machine_x21) (call_after) (tx_final) (tx_final_done) (tx_final_images) (tx_final_rest))
    (fp_machineAt04b8_slot1_ForwardA0N0_Hist (args) (returnAddress) (call2_outcome) (machine_x21) (call_after) (tx_final) (tx_final_done) (tx_final_images) (tx_final_rest))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt04f4_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_791c5acc1109e8e6 & forward_witness_88383840afa7af74 & forward_witness_d77b5950a2aea933 & forward_witness_87e5cadc5c04d5d4 & forward_witness_1492ef7bd46b3b7a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt04b8_slot1_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_791c5acc1109e8e6, forward_witness_88383840afa7af74, (BV 64%N 0%Z).
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
  split; [exact HF20|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF23|].
  split; [exact HF24|].
  by vm_compute.
Qed.

End edges.
