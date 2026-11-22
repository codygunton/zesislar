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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cEntries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot026cStructural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0270Structural.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeObligations.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt026c_ForwardA0N0 -> fp_machineAt0270_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_58 (args : ParentHeaderArgs) (returnAddress : Z) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (join_resource_32_call_after_call_after_call_output_bytes : list byte) (machine_x10_succ : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt026c_ForwardA0N0_Hist (args) (returnAddress) (call10_after) (call_after))
    (fp_machineAt0270_ForwardA0N0_Hist (args) (returnAddress) (machine_x10_succ) (call10_after) (call_after))
    (⌜((0%Z <= bv_unsigned machine_x10_succ <= 65535%Z)%Z)⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10_succ >= bv_unsigned (BV 64%N 0%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) >= (0%Z))%Z))⌝ ∗ ⌜((bool_decide ((bv_unsigned machine_x10_succ <= bv_unsigned (BV 64%N 65535%Z))%Z)) = true) /\ ((((bv_unsigned machine_x10_succ) <= (65535%Z))%Z))⌝ ∗ ⌜(bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args)⌝ ∗ ⌜((bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((List.length call_after = 40)%nat)⌝ ∗ ⌜((List.length call10_after = 40)%nat)⌝ ∗ ⌜((List.length join_resource_32_call_after_call_after_call_output_bytes = 40)%nat)⌝ ∗ ⌜machine_x10_succ = (BV 64%N 3%Z)⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. pose proof Hh as HS. unfold fp_machineAt026c_ForwardA0N0_Hist in Hh.
  destruct Hh as (fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20).
  iIntros "HN".
  iDestruct "HN" as "(%HN0 & %HN1 & %HN2 & %HV0 & %HV1 & %HV2 & %HV3 & %HV4 & %HE0 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0270_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_d77b5950a2aea933, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HN0|].
  split; [exact HF3|].
  split; [exact (fp_edge026c_0270_ErrorTag_holds args returnAddress call10_after call_after join_resource_32_call_after_call_after_call_output_bytes machine_x10_succ HS HV0 HV1 HV2 HV3 HV4 HE0)|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HN1|].
  exact HN2.
Qed.

End edges.
