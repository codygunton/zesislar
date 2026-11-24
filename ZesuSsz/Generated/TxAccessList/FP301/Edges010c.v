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
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Export ZesuSsz.Compliance.TxAccessListHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot010cEntries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot010cStructural.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0114Entries.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0114Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt010c_ForwardA0N0 -> fp_machineAt0114_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_9 (args : TxAccessListArgs) (returnAddress : Z) (call3_after : DecodeItemOutcome) (call3_kept_x22 : bv 64) (call3_kept_x23 : bv 64) (call3_kept_x26 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x23 : bv 64) (call_after : DecodeItemOutcome) (outer_x20 : bv 64) (outer_x21 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt010c_ForwardA0N0_Hist (args) (returnAddress) (call2_after) (call_after) (outer_x20) (outer_x21))
    (fp_machineAt0114_ForwardA0N0_Hist (args) (returnAddress) (call3_after) (call3_kept_x22) (call3_kept_x23) (call3_kept_x26) (call2_after) (call_after) (outer_x20) (outer_x21))
    (⌜((bool_decide ((bv_zero_extend 64%N (bv_concat 16%N (List.nth 33%nat call3_after (BV 8%N 0%Z)) (List.nth 32%nat call3_after (BV 8%N 0%Z)))) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_concat 16%N (List.nth 33%nat call3_after (BV 8%N 0%Z)) (List.nth 32%nat call3_after (BV 8%N 0%Z)))) = (0%Z))%Z))⌝ ∗ ⌜((zesu_named_eq call2_kept_x23 (bv_add (txInputPointer args) (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call_after (BV 8%N 0%Z)) (List.nth 30%nat call_after (BV 8%N 0%Z))) (List.nth 29%nat call_after (BV 8%N 0%Z))) (List.nth 28%nat call_after (BV 8%N 0%Z))) (List.nth 27%nat call_after (BV 8%N 0%Z))) (List.nth 26%nat call_after (BV 8%N 0%Z))) (List.nth 25%nat call_after (BV 8%N 0%Z))) (List.nth 24%nat call_after (BV 8%N 0%Z))))))⌝ ∗ ⌜((zesu_named_eq call3_kept_x22 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call2_after (BV 8%N 0%Z)) (List.nth 14%nat call2_after (BV 8%N 0%Z))) (List.nth 13%nat call2_after (BV 8%N 0%Z))) (List.nth 12%nat call2_after (BV 8%N 0%Z))) (List.nth 11%nat call2_after (BV 8%N 0%Z))) (List.nth 10%nat call2_after (BV 8%N 0%Z))) (List.nth 9%nat call2_after (BV 8%N 0%Z))) (List.nth 8%nat call2_after (BV 8%N 0%Z)))))⌝ ∗ ⌜((zesu_named_eq call3_kept_x23 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call2_after (BV 8%N 0%Z)) (List.nth 6%nat call2_after (BV 8%N 0%Z))) (List.nth 5%nat call2_after (BV 8%N 0%Z))) (List.nth 4%nat call2_after (BV 8%N 0%Z))) (List.nth 3%nat call2_after (BV 8%N 0%Z))) (List.nth 2%nat call2_after (BV 8%N 0%Z))) (List.nth 1%nat call2_after (BV 8%N 0%Z))) (List.nth 0%nat call2_after (BV 8%N 0%Z)))))⌝ ∗ ⌜((zesu_named_eq call3_kept_x26 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call2_after (BV 8%N 0%Z)) (List.nth 30%nat call2_after (BV 8%N 0%Z))) (List.nth 29%nat call2_after (BV 8%N 0%Z))) (List.nth 28%nat call2_after (BV 8%N 0%Z))) (List.nth 27%nat call2_after (BV 8%N 0%Z))) (List.nth 26%nat call2_after (BV 8%N 0%Z))) (List.nth 25%nat call2_after (BV 8%N 0%Z))) (List.nth 24%nat call2_after (BV 8%N 0%Z)))))⌝ ∗ ⌜(∃ (call3_arg_x13 : bv 64) (call3_arg_x14 : bv 64) (call3_arg_x15 : bv 64) (call3_arg_x16 : bv 64) (call3_arg_x17 : bv 64) (call3_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551232%Z))); (call3_kept_x23); (call3_kept_x22); (call3_arg_x13); (call3_arg_x14); (call3_arg_x15); (call3_arg_x16); (call3_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (take (Z.to_nat (bv_unsigned (call3_kept_x22))) (drop (Z.to_nat (bv_unsigned (call3_kept_x23) - bv_unsigned (txInputPointer args))) (txInputBytes args))) call3_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551232%Z))); (call3_kept_x23); (call3_kept_x22); (call3_arg_x13); (call3_arg_x14); (call3_arg_x15); (call3_arg_x16); (call3_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (take (Z.to_nat (bv_unsigned (call3_kept_x22))) (drop (Z.to_nat (bv_unsigned (call3_kept_x23) - bv_unsigned (txInputPointer args))) (txInputBytes args))) call3_before) (call3_after)))⌝ ∗ ⌜((bv_unsigned (txInputPointer args) <= bv_unsigned (call3_kept_x23) /\ bv_unsigned (call3_kept_x23) + bv_unsigned (call3_kept_x22) <= bv_unsigned (txInputPointer args) + Z.of_nat (List.length (txInputBytes args)))%Z)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt010c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_791c5acc1109e8e6 & forward_witness_f1505c797ad3010d & forward_witness_d7543602bfbbe148 & forward_witness_83d3e6d46c3de70e & forward_witness_1d218312837c2f84 & forward_witness_dc636cab9ffb40ae & forward_witness_184f6fc7524c683f & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_407fca3a6f90b8db & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_d0511cb7161d8dd4 & forward_witness_0c9a8614ab622b44 & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HV4 & %HV6 & %HV7 & %HV8 & %HV9 & %HV10 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0114_ForwardA0N0_Hist.
  exists call2_kept_x23, (BV 64%N 0%Z), forward_witness_791c5acc1109e8e6, forward_witness_f1505c797ad3010d, forward_witness_d7543602bfbbe148, forward_witness_83d3e6d46c3de70e, forward_witness_1d218312837c2f84, forward_witness_dc636cab9ffb40ae, forward_witness_184f6fc7524c683f, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_407fca3a6f90b8db, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_d0511cb7161d8dd4, forward_witness_0c9a8614ab622b44, forward_witness_cbcac9df79b9221c, forward_witness_1be931110d776902.
  split; [exact HF0|].
  split; [exact HV4|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HV6|].
  split; [exact HV7|].
  split; [exact HV8|].
  split; [exact HV9|].
  split; [exact HV10|].
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
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  exact HN0.
Qed.

End edges.
