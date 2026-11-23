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
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot008cEntries.
Require Import ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot008cStructural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt008c_slot0_ForwardA0N0 -> fp_machineReturn_slot0_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_8 (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt008c_slot0_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineReturn_slot0_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt008c_slot0_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_1be931110d776902 & forward_witness_55ab0ce59750150a & HF0 & HF1 & HF2 & HF3 & HF4).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot0_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_72b7e22ed74cb83b, forward_witness_1be931110d776902, forward_witness_55ab0ce59750150a, (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  by vm_compute.
Qed.

(* fp_machineAt008c_slot1_ForwardA0N0 -> fp_machineReturn_slot1_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_9 (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (uninit_byte_0a19abea1fa0cb16 : bv 8) (uninit_byte_6568a977e3726114 : bv 8) (uninit_byte_896c78ef7fc1d203 : bv 8) (uninit_byte_b5ac3c8a69f5ac5f : bv 8) (uninit_byte_83ab782bb3e943d7 : bv 8) (uninit_byte_a7ca23dbcbd67004 : bv 8) (uninit_byte_d0d9840f8bab249d : bv 8) (uninit_byte_b58fbbc0e17a0d19 : bv 8) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt008c_slot1_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineReturn_slot1_ForwardA0N0_Hist (args) (returnAddress) (uninit_byte_0a19abea1fa0cb16) (uninit_byte_6568a977e3726114) (uninit_byte_896c78ef7fc1d203) (uninit_byte_b5ac3c8a69f5ac5f) (uninit_byte_83ab782bb3e943d7) (uninit_byte_a7ca23dbcbd67004) (uninit_byte_d0d9840f8bab249d) (uninit_byte_b58fbbc0e17a0d19))
    (⌜((negb (bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_0a19abea1fa0cb16 uninit_byte_6568a977e3726114) uninit_byte_896c78ef7fc1d203) uninit_byte_b5ac3c8a69f5ac5f) uninit_byte_83ab782bb3e943d7) uninit_byte_a7ca23dbcbd67004) uninit_byte_d0d9840f8bab249d) uninit_byte_b58fbbc0e17a0d19) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 1%Z)))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_0a19abea1fa0cb16 uninit_byte_6568a977e3726114) uninit_byte_896c78ef7fc1d203) uninit_byte_b5ac3c8a69f5ac5f) uninit_byte_83ab782bb3e943d7) uninit_byte_a7ca23dbcbd67004) uninit_byte_d0d9840f8bab249d) uninit_byte_b58fbbc0e17a0d19) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) <> (1%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_0a19abea1fa0cb16 uninit_byte_6568a977e3726114) uninit_byte_896c78ef7fc1d203) uninit_byte_b5ac3c8a69f5ac5f) uninit_byte_83ab782bb3e943d7) uninit_byte_a7ca23dbcbd67004) uninit_byte_d0d9840f8bab249d) uninit_byte_b58fbbc0e17a0d19) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 0%Z))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_0a19abea1fa0cb16 uninit_byte_6568a977e3726114) uninit_byte_896c78ef7fc1d203) uninit_byte_b5ac3c8a69f5ac5f) uninit_byte_83ab782bb3e943d7) uninit_byte_a7ca23dbcbd67004) uninit_byte_d0d9840f8bab249d) uninit_byte_b58fbbc0e17a0d19) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) = (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt008c_slot1_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_1be931110d776902 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_87e5cadc5c04d5d4 & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot1_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), forward_witness_72b7e22ed74cb83b, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_88383840afa7af74, (BV 64%N 0%Z).
  split; [by vm_compute|].
  split; [exact HF1|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF13|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [exact HN0|].
  exact HN1.
Qed.

(* fp_machineAt008c_slot2_ForwardA0N0 -> fp_machineReturn_slot2_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_10 (args : KeysEnsureCapacityBlockArgs) (returnAddress : Z) (call_x10 : bv 64) (uninit_byte_5698869aee9d67fc : bv 8) (uninit_byte_95bf6d5ee8eb0dbd : bv 8) (uninit_byte_31cae7df4f765f47 : bv 8) (uninit_byte_cb7f86138f242139 : bv 8) (uninit_byte_7253aafc7827ab1a : bv 8) (uninit_byte_c2b6b669adb1f4a4 : bv 8) (uninit_byte_fbe60982c53c8a95 : bv 8) (uninit_byte_eb88f8ef5356ddbf : bv 8) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt008c_slot2_ForwardA0N0_Hist (args) (returnAddress) (call_x10))
    (fp_machineReturn_slot2_ForwardA0N0_Hist (args) (returnAddress) (call_x10) (uninit_byte_5698869aee9d67fc) (uninit_byte_95bf6d5ee8eb0dbd) (uninit_byte_31cae7df4f765f47) (uninit_byte_cb7f86138f242139) (uninit_byte_7253aafc7827ab1a) (uninit_byte_c2b6b669adb1f4a4) (uninit_byte_fbe60982c53c8a95) (uninit_byte_eb88f8ef5356ddbf))
    (⌜((negb (bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_5698869aee9d67fc uninit_byte_95bf6d5ee8eb0dbd) uninit_byte_31cae7df4f765f47) uninit_byte_cb7f86138f242139) uninit_byte_7253aafc7827ab1a) uninit_byte_c2b6b669adb1f4a4) uninit_byte_fbe60982c53c8a95) uninit_byte_eb88f8ef5356ddbf) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 1%Z)))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_5698869aee9d67fc uninit_byte_95bf6d5ee8eb0dbd) uninit_byte_31cae7df4f765f47) uninit_byte_cb7f86138f242139) uninit_byte_7253aafc7827ab1a) uninit_byte_c2b6b669adb1f4a4) uninit_byte_fbe60982c53c8a95) uninit_byte_eb88f8ef5356ddbf) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) <> (1%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_5698869aee9d67fc uninit_byte_95bf6d5ee8eb0dbd) uninit_byte_31cae7df4f765f47) uninit_byte_cb7f86138f242139) uninit_byte_7253aafc7827ab1a) uninit_byte_c2b6b669adb1f4a4) uninit_byte_fbe60982c53c8a95) uninit_byte_eb88f8ef5356ddbf) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 0%Z))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_5698869aee9d67fc uninit_byte_95bf6d5ee8eb0dbd) uninit_byte_31cae7df4f765f47) uninit_byte_cb7f86138f242139) uninit_byte_7253aafc7827ab1a) uninit_byte_c2b6b669adb1f4a4) uninit_byte_fbe60982c53c8a95) uninit_byte_eb88f8ef5356ddbf) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) = (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt008c_slot2_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_a84be01a9be85bdb & forward_witness_9644ccf41f39915a & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_cbcac9df79b9221c & forward_witness_72b7e22ed74cb83b & forward_witness_21649d1cf161453f & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot2_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_11fde2df72db9d06, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_1492ef7bd46b3b7a, forward_witness_72b7e22ed74cb83b, (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF12|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF13|].
  split; [exact HF21|].
  split; [exact HF22|].
  split; [exact HF24|].
  split; [by vm_compute|].
  split; [exact HN0|].
  exact HN1.
Qed.

End edges.
