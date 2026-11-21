(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Contracts.ParentHeaderWalkFact.
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00b0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0408Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0408_ForwardA0N0 -> fp_machineAt00b0_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_106 (args : ParentHeaderArgs) (returnAddress : Z) (machine_x10 : bv 64) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x10_succ : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0408_ForwardA0N0_Hist (args) (returnAddress) (machine_x10) (machine_x21_1) (machine_x22_1) (call13_after) (call10_after) (call_after))
    (fp_machineAt00b0_ForwardA0N0_Hist (args) (returnAddress) (machine_x10_succ))
    (⌜((2148617472%Z <= bv_unsigned machine_x10_succ <= 2148618660%Z)%Z)⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10_succ >= bv_unsigned (BV 64%N 2148617472%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) >= (2148617472%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10_succ <= bv_unsigned (BV 64%N 2148618660%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) <= (2148618660%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0408_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt00b0_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933.
  split; [exact HN0|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF25|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF21|].
  split; [exact HF24|].
  split; [exact HN1|].
  exact HN2.
Qed.

Global Instance zesu_hist_reveal_38 (args : ParentHeaderArgs) (returnAddress : Z) (machine_x10 : bv 64) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) (call13_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt0408_ForwardA0N0_Hist (args) (returnAddress) (machine_x10) (machine_x21_1) (machine_x22_1) (call13_after) (call10_after) (call_after)) ((∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551224%Z))); ((parentHeaderInputPointer args)); ((parentHeaderInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (parentHeaderInputBytes args) call_before) (call_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0408_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & forward_witness_a84be01a9be85bdb & forward_witness_407fca3a6f90b8db & forward_witness_88383840afa7af74 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28).
  exact HF0.
Qed.

End edges.
