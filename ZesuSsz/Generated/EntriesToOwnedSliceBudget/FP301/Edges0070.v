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
Require Import ZesuSsz.Automation2.StepBudget.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0070Entries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0070Structural.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot012cEntries.
Require Import ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot012cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0070_ForwardA0N0 -> fp_machineAt012c_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_6 (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) (machine_x10_succ : bv 64) (machine_x23 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0070_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineAt012c_ForwardA0N0_Hist (args) (returnAddress) (machine_x10_succ) (machine_x23))
    (⌜((0%Z <= bv_unsigned machine_x10_succ <= 0%Z)%Z)⌝ ∗ ⌜(((((((bv_unsigned ((Z_to_bv 64%N (arrayListCapacity (entriesBlockList args))))) = (0%Z))%Z) \/ ((((bv_unsigned ((Z_to_bv 64%N (arrayListCapacity (entriesBlockList args))))) <> (0%Z))%Z) /\ (((bv_unsigned (bv_extract 64%N 64%N (bv_mul (bv_zero_extend 128%N ((Z_to_bv 64%N (arrayListLength (entriesBlockList args))))) (BV 128%N 40%Z)))) <> (0%Z))%Z))) /\ (((bv_unsigned machine_x23) = (bv_unsigned (savedX23 (toOwnedSaved (entriesBase args)))))%Z)) \/ ((((bv_unsigned ((Z_to_bv 64%N (arrayListCapacity (entriesBlockList args))))) <> (0%Z))%Z) /\ (((bv_unsigned (bv_extract 64%N 64%N (bv_mul (bv_zero_extend 128%N ((Z_to_bv 64%N (arrayListLength (entriesBlockList args))))) (BV 128%N 40%Z)))) = (0%Z))%Z) /\ (((bv_unsigned machine_x23) = (bv_unsigned (bv_add (bv_shiftl ((Z_to_bv 64%N (arrayListLength (entriesBlockList args)))) (BV 64%N 5%Z)) (bv_shiftl ((Z_to_bv 64%N (arrayListLength (entriesBlockList args)))) (BV 64%N 3%Z)))))%Z))))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10_succ >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10_succ <= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) <= (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0070_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HN3 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt012c_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_72b7e22ed74cb83b, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, (BV 64%N 0%Z).
  split; [exact HN0|].
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [by vm_compute|].
  split; [exact HN1|].
  split; [exact HN2|].
  exact HN3.
Qed.

End edges.
