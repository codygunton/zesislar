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
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Export ZesuSsz.Compliance.KeysEnsureCapacityHints.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Automation2.StepBudget.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0164Entries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0164Structural.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot017cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot017cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0164_ForwardA0N0 -> fp_machineAt017c_ForwardA0N0 (call_return) *)
Global Instance zesu_hist_edge_22 (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (call_x10 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0164_ForwardA0N0_Hist (args) (returnAddress) (call_x10))
    (fp_machineAt017c_ForwardA0N0_Hist (args) (returnAddress) (call_x10))
    (⌜(((ziskWord ((bv_unsigned (call_x10))) /\ ziskWord ((bv_unsigned (((Z_to_bv 64%N (arrayListPointer (ensureBlockList args))))))) /\ ziskWord ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (ensureBlockList args)))) (BV 64%N 5%Z))))) /\
  ziskWritableSection stockZiskPermissions ziskExtraParamsAddress 8 /\
  (((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (ensureBlockList args)))) (BV 64%N 5%Z))))) <> 0 ->
    ziskMemcpyRange ((bv_unsigned (call_x10))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (ensureBlockList args)))) (BV 64%N 5%Z))))) /\
    ziskMemcpyRange ((bv_unsigned (((Z_to_bv 64%N (arrayListPointer (ensureBlockList args))))))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (ensureBlockList args)))) (BV 64%N 5%Z))))) /\
    ziskWritableSection stockZiskPermissions ((bv_unsigned (((Z_to_bv 64%N (arrayListPointer (ensureBlockList args))))))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (ensureBlockList args)))) (BV 64%N 5%Z))))) /\
    ziskWritableSection stockZiskPermissions ((bv_unsigned (call_x10))) ((bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (ensureBlockList args)))) (BV 64%N 5%Z)))))))) /\ (Z.of_nat (length (arrayListItems (ensureBlockList args))) = bv_unsigned ((bv_shiftl ((Z_to_bv 64%N (arrayListLength (ensureBlockList args)))) (BV 64%N 5%Z)))) /\ (length (ensureScratchBefore (ensureBase args)) = 8%nat))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0164_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_1be931110d776902 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_87e5cadc5c04d5d4 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_a84be01a9be85bdb & forward_witness_9644ccf41f39915a & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_cbcac9df79b9221c & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt017c_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_87e5cadc5c04d5d4, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_a84be01a9be85bdb, forward_witness_9644ccf41f39915a, forward_witness_407fca3a6f90b8db, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_cbcac9df79b9221c.
  split; [exact HN0|].
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
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF22|].
  exact HF20.
Qed.

End edges.
