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
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnStructural.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Entries.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0118Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0118_slot0_ForwardA0N0 -> fp_machineReturn_slot0_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_20 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (uninit_byte_c430781a9c8f7c00 : bv 8) (uninit_byte_cf60ff57de228668 : bv 8) (uninit_byte_759f6803563c7bca : bv 8) (uninit_byte_490bd74478998b3e : bv 8) (uninit_byte_b626fdd45011c35c : bv 8) (uninit_byte_5bc31d7c3873f550 : bv 8) (uninit_byte_3de86c72116636b0 : bv 8) (uninit_byte_bbb5699fa9bcc82e : bv 8) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0118_slot0_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineReturn_slot0_ForwardA0N0_Hist (args) (returnAddress) (uninit_byte_c430781a9c8f7c00) (uninit_byte_cf60ff57de228668) (uninit_byte_759f6803563c7bca) (uninit_byte_490bd74478998b3e) (uninit_byte_b626fdd45011c35c) (uninit_byte_5bc31d7c3873f550) (uninit_byte_3de86c72116636b0) (uninit_byte_bbb5699fa9bcc82e))
    (⌜((negb (bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_c430781a9c8f7c00 uninit_byte_cf60ff57de228668) uninit_byte_759f6803563c7bca) uninit_byte_490bd74478998b3e) uninit_byte_b626fdd45011c35c) uninit_byte_5bc31d7c3873f550) uninit_byte_3de86c72116636b0) uninit_byte_bbb5699fa9bcc82e) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 1%Z)))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_c430781a9c8f7c00 uninit_byte_cf60ff57de228668) uninit_byte_759f6803563c7bca) uninit_byte_490bd74478998b3e) uninit_byte_b626fdd45011c35c) uninit_byte_5bc31d7c3873f550) uninit_byte_3de86c72116636b0) uninit_byte_bbb5699fa9bcc82e) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) <> (1%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_c430781a9c8f7c00 uninit_byte_cf60ff57de228668) uninit_byte_759f6803563c7bca) uninit_byte_490bd74478998b3e) uninit_byte_b626fdd45011c35c) uninit_byte_5bc31d7c3873f550) uninit_byte_3de86c72116636b0) uninit_byte_bbb5699fa9bcc82e) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 0%Z))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_c430781a9c8f7c00 uninit_byte_cf60ff57de228668) uninit_byte_759f6803563c7bca) uninit_byte_490bd74478998b3e) uninit_byte_b626fdd45011c35c) uninit_byte_5bc31d7c3873f550) uninit_byte_3de86c72116636b0) uninit_byte_bbb5699fa9bcc82e) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) = (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0118_slot0_ForwardA0N0_Hist in Hh.
  destruct Hh as (machine_x10 & fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_87e5cadc5c04d5d4 & forward_witness_d77b5950a2aea933 & forward_witness_72b7e22ed74cb83b & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot0_ForwardA0N0_Hist.
  exists machine_x10, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_72b7e22ed74cb83b.
  split; [exact HF0|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HN0|].
  exact HN1.
Qed.

(* fp_machineAt0118_slot1_ForwardA0N0 -> fp_machineReturn_slot1_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_21 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0118_slot1_ForwardA0N0_Hist (args) (returnAddress))
    (fp_machineReturn_slot1_ForwardA0N0_Hist (args) (returnAddress))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0118_slot1_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_72b7e22ed74cb83b & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_8da77898f656116a & forward_witness_eba071f2aafca867 & forward_witness_6b5c9f21ea2547d9 & forward_witness_1b5321dec05d0d89 & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot1_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_72b7e22ed74cb83b, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_8da77898f656116a, forward_witness_eba071f2aafca867, forward_witness_6b5c9f21ea2547d9, forward_witness_1b5321dec05d0d89, forward_witness_9644ccf41f39915a, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF14|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [by vm_compute|].
  by vm_compute.
Qed.

(* fp_machineAt0118_slot2_ForwardA0N0 -> fp_machineReturn_slot2_ForwardA0N0 (return) *)
Global Instance zesu_hist_edge_22 (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (call_x10 : bv 64) (call_x13 : bv 64) (call_x14 : bv 64) (call_x15 : bv 64) (call_x16 : bv 64) (call_x17 : bv 64) (uninit_byte_a77337468c36ada6 : bv 8) (uninit_byte_189c6677cfea250d : bv 8) (uninit_byte_f984c40b213d2079 : bv 8) (uninit_byte_c550530795db8dfd : bv 8) (uninit_byte_8c6db027d1f220ef : bv 8) (uninit_byte_125ce99c76b56a45 : bv 8) (uninit_byte_35603b88f81f3afd : bv 8) (uninit_byte_4925068b1df1186b : bv 8) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0118_slot2_ForwardA0N0_Hist (args) (returnAddress) (call_x10) (call_x13) (call_x14) (call_x15) (call_x16) (call_x17))
    (fp_machineReturn_slot2_ForwardA0N0_Hist (args) (returnAddress) (call_x10) (call_x13) (call_x14) (call_x15) (call_x16) (call_x17) (uninit_byte_a77337468c36ada6) (uninit_byte_189c6677cfea250d) (uninit_byte_f984c40b213d2079) (uninit_byte_c550530795db8dfd) (uninit_byte_8c6db027d1f220ef) (uninit_byte_125ce99c76b56a45) (uninit_byte_35603b88f81f3afd) (uninit_byte_4925068b1df1186b))
    (⌜((negb (bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_a77337468c36ada6 uninit_byte_189c6677cfea250d) uninit_byte_f984c40b213d2079) uninit_byte_c550530795db8dfd) uninit_byte_8c6db027d1f220ef) uninit_byte_125ce99c76b56a45) uninit_byte_35603b88f81f3afd) uninit_byte_4925068b1df1186b) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 1%Z)))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_a77337468c36ada6 uninit_byte_189c6677cfea250d) uninit_byte_f984c40b213d2079) uninit_byte_c550530795db8dfd) uninit_byte_8c6db027d1f220ef) uninit_byte_125ce99c76b56a45) uninit_byte_35603b88f81f3afd) uninit_byte_4925068b1df1186b) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) <> (1%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_a77337468c36ada6 uninit_byte_189c6677cfea250d) uninit_byte_f984c40b213d2079) uninit_byte_c550530795db8dfd) uninit_byte_8c6db027d1f220ef) uninit_byte_125ce99c76b56a45) uninit_byte_35603b88f81f3afd) uninit_byte_4925068b1df1186b) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z))) = (BV 1%N 0%Z))) = true) /\ ((((bv_unsigned (bv_extract 0%N 1%N (bv_shiftr (bv_and (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N uninit_byte_a77337468c36ada6 uninit_byte_189c6677cfea250d) uninit_byte_f984c40b213d2079) uninit_byte_c550530795db8dfd) uninit_byte_8c6db027d1f220ef) uninit_byte_125ce99c76b56a45) uninit_byte_35603b88f81f3afd) uninit_byte_4925068b1df1186b) (BV 64%N 18446744073709551614%Z)) (BV 64%N 1%Z)))) = (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0118_slot2_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_d7543602bfbbe148 & forward_witness_00470b017f14ddbf & forward_witness_83d3e6d46c3de70e & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineReturn_slot2_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_d7543602bfbbe148, forward_witness_00470b017f14ddbf, forward_witness_83d3e6d46c3de70e, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF11|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF12|].
  split; [exact HF16|].
  split; [exact HF18|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [exact HN0|].
  exact HN1.
Qed.

End edges.
