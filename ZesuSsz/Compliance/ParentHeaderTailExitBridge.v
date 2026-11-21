(* decodeParentHeader end bridge of the memcpy tail exit (exit design A): the
   generated package of the memcpy tail join 0x00b0 gives the contract exit.
   The meaning is an explicit premise in the form of plan step 2.4 (M1): the
   exit's history implies the meaning of its result. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Compliance.ParentHeaderExitBridgeTactics.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.
Local Open Scope Z_scope.
(* reg_col stays folded while the exit resources are framed. *)
#[local] Typeclasses Opaque reg_col.

(* The meaning premise of the memcpy tail exit. *)
Definition parentHeaderTailExitMeaning : Prop :=
  forall (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome),
    bv_unsigned (parentHeaderReturnAddress args) = returnAddress ->
    parentHeaderArgsWellFormed args ->
    zesu_hist (ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8_ForwardA0N0_Hist
      args returnAddress call_after) ->
    ParentHeaderMeaningModuloKnownBugs (parentHeaderCall args) (parentHeaderMemcpySourceBefore args).

Lemma parentHeader_tail_end_bridge `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) :
  parentHeaderTailExitMeaning ->
  parentHeaderEndBridge args returnAddress
    (ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8_ForwardA0N0
      args returnAddress).
Proof.
  intros Hmeaning.
  rewrite /ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8_ForwardA0N0.
  parentHeader_exit_open.
  parentHeader_exit_close ParentHeaderMemcpyTail.
  eapply Hmeaning; eassumption.
Qed.
