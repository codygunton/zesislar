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
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f8Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00f8Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot00fcStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt00f8_ForwardA0N0 -> fp_machineAt00fc_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_16 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (call_x10 : bv 64) (machine_x23 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt00f8_ForwardA0N0_Hist (args) (returnAddress) (call_x10))
    (fp_machineAt00fc_ForwardA0N0_Hist (args) (returnAddress) (call_x10) (machine_x23))
    (⌜((0%Z <= bv_unsigned call_x10 <= 0%Z)%Z)⌝ ∗ ⌜(((((((bv_unsigned ((Z_to_bv 64%N (arrayListCapacity (keysBlockList args))))) = (0%Z))%Z) \/ ((((bv_unsigned ((Z_to_bv 64%N (arrayListCapacity (keysBlockList args))))) <> (0%Z))%Z) /\ (((bv_unsigned (bv_shiftr ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 59%Z))) <> (0%Z))%Z))) /\ (((bv_unsigned machine_x23) = (bv_unsigned ((Z_to_bv 64%N (arrayListLength (keysBlockList args))))))%Z)) \/ ((((bv_unsigned ((Z_to_bv 64%N (arrayListCapacity (keysBlockList args))))) <> (0%Z))%Z) /\ (((bv_unsigned (bv_shiftr ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 59%Z))) = (0%Z))%Z) /\ (((bv_unsigned machine_x23) = (bv_unsigned (bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z))))%Z))))⌝ ∗ ⌜((bool_decide ((bv_unsigned call_x10 >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned call_x10) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned call_x10 <= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned call_x10) <= (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt00f8_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_8da77898f656116a & forward_witness_6b5c9f21ea2547d9 & forward_witness_1b5321dec05d0d89 & forward_witness_c2f9141038c5af1e & forward_witness_13733e317af04159 & forward_witness_8b04c47a270882cf & forward_witness_acd02f915d5d3e8c & forward_witness_e25a2671f181dd12 & forward_witness_10de015b43615ae8 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HN3 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00fc_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_72b7e22ed74cb83b, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, (BV 64%N 0%Z).
  split; [exact HN0|].
  split; [exact HF20|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [by vm_compute|].
  split; [exact HN1|].
  split; [exact HN2|].
  exact HN3.
Qed.

End edges.
