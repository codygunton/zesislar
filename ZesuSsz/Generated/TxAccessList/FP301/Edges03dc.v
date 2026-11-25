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
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03dcEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot03dcStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot04a8Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt03dc_ForwardA0N0 -> fp_machineAt04a8_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_60 (args : TxAccessListArgs) (returnAddress : Z) (call6_x10 : bv 64) (call5_outcome : ToOwnedSliceOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) (call3_kept_x26 : bv 64) (call4_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_payload_offset : Z) (call2_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (tx_entries : ArrayListState) (tx_done : list AccessListEntryValue) (tx_images : list TxAccessListEntryImage) (tx_keys_done : ArrayListState) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt03dc_ForwardA0N0_Hist (args) (returnAddress) (call6_x10) (call5_outcome) (outer_x20) (outer_x21) (call3_kept_x26) (call4_after) (call3_after) (call3_payload_offset) (call2_after) (call_after) (tx_entries) (tx_done) (tx_images) (tx_keys_done))
    (fp_machineAt04a8_ForwardA0N0_Hist (args) (returnAddress) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt03dc_ForwardA0N0_Hist in Hh.
  destruct Hh as (tx_scratch & tx_keys_list & machine_x10 & fp_seed_mstatus_bits & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_00470b017f14ddbf & forward_witness_8da77898f656116a & forward_witness_eba071f2aafca867 & forward_witness_6b5c9f21ea2547d9 & forward_witness_1b5321dec05d0d89 & forward_witness_72b7e22ed74cb83b & forward_witness_87e5cadc5c04d5d4 & forward_witness_1492ef7bd46b3b7a & forward_witness_407fca3a6f90b8db & forward_witness_cbcac9df79b9221c & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt04a8_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f.
  split; [exact HF0|].
  split; [exact HF73|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF20|].
  exact HF21.
Qed.

End edges.
