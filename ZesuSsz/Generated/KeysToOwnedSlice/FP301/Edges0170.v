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
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0170Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0170Structural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0184Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0184Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0170_ForwardA0N0 -> fp_machineAt0184_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_27 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (call_x10 : bv 64) (call_x13 : bv 64) (call_x14 : bv 64) (call_x15 : bv 64) (call_x16 : bv 64) (call_x17 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0170_ForwardA0N0_Hist (args) (returnAddress) (call_x10))
    (fp_machineAt0184_ForwardA0N0_Hist (args) (returnAddress) (call_x10) (call_x13) (call_x14) (call_x15) (call_x16) (call_x17))
    (⌜((Z.of_nat (List.length (word64Bytes (bv_unsigned (([(call_x10); (((Z_to_bv 64%N (arrayListPointer (keysBlockList args))))); ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z))); (call_x13); (call_x14); (call_x15); (call_x16); (call_x17)]) !!! 2%nat)))) = 8)%Z)⌝ ∗ ⌜((Z.of_nat (List.length (arrayListItems (keysBlockList args))) = altFlAllocatedBytes (bv_unsigned call_x10) (bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z)))))%Z)⌝ ∗ ⌜(((ziskWord ((bv_unsigned (call_x10))) /\ ziskWord ((bv_unsigned (((Z_to_bv 64%N (arrayListPointer (keysBlockList args))))))) /\ ziskWord ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z))))) /\
  ziskWritableSection stockZiskPermissions ziskExtraParamsAddress 8 /\
  (((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z))))) <> 0 ->
    ziskMemcpyRange ((bv_unsigned (call_x10))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z))))) /\
    ziskMemcpyRange ((bv_unsigned (((Z_to_bv 64%N (arrayListPointer (keysBlockList args))))))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z))))) /\
    ziskWritableSection stockZiskPermissions ((bv_unsigned (((Z_to_bv 64%N (arrayListPointer (keysBlockList args))))))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z))))) /\
    ziskWritableSection stockZiskPermissions ((bv_unsigned (call_x10))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z)))))))) /\ (Z.of_nat (length (arrayListItems (keysBlockList args))) = bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) (BV 64%N 5%Z)))) /\ (length (toOwnedScratchBefore (keysBase args)) = 8%nat))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0170_ForwardA0N0_Hist in Hh.
  destruct Hh as (machine_x10 & machine_x23 & fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_88383840afa7af74 & forward_witness_87e5cadc5c04d5d4 & forward_witness_d77b5950a2aea933 & forward_witness_a84be01a9be85bdb & forward_witness_21649d1cf161453f & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_72b7e22ed74cb83b & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0184_ForwardA0N0_Hist.
  exists machine_x10, machine_x23, fp_seed_mstatus_bits, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_88383840afa7af74, forward_witness_d77b5950a2aea933, forward_witness_a84be01a9be85bdb, forward_witness_21649d1cf161453f, forward_witness_407fca3a6f90b8db, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_72b7e22ed74cb83b, (BV 64%N 0%Z).
  split; [exact HN0|].
  split; [exact HN1|].
  split; [exact HN2|].
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
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [by vm_compute|].
  exact HF18.
Qed.

End edges.
