(* decodeParentHeader end bridge of the direct return through slot 3 of the
   duplicated return block 0x0274 (exit design A): its generated return package
   gives the contract exit. One module per slot (each bridge takes minutes). One shared tactic (ParentHeaderExitBridgeTactics.v)
   for every slot: the slots differ only in the stored bytes, so the frame and
   the result are folded by address. The meaning of each slot's result is the
   package's generated exit-meaning premise at the contract meaning. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Compliance.ParentHeaderExitBridgeTactics.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.
Local Open Scope Z_scope.
(* reg_col stays folded while the exit resources are framed. *)
#[local] Typeclasses Opaque reg_col.

Lemma parentHeader_direct_end_bridge_slot3 `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) :
  ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0_ExitMeaning
    parentHeaderResultMeaning ->
  parentHeaderEndBridge args returnAddress
    (ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0
      args returnAddress).
Proof.
  intros Hmeaning.
  rewrite /ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0.
  parentHeader_direct_slot_bridge Hmeaning.
Qed.
