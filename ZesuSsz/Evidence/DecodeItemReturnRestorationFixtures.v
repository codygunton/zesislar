Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma registeredDecodeItemSavedReturnDecoder (args : DecodeItemArgs) (frameBytes : list byte) (Hframe : decodeItemSavedFrameFacts args frameBytes) :
Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  Z_to_bv 64%N (decodeItemReturnAddress args).
Proof. zesu_witness_facts. assumption. Qed.
Print Assumptions registeredDecodeItemSavedReturnDecoder.

Lemma registeredDecodeItemSavedFramePointerDecoder (args : DecodeItemArgs) (frameBytes : list byte) (Hframe : decodeItemSavedFrameFacts args frameBytes) :
Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  decodeItemSavedFramePointer args.
Proof. zesu_witness_facts. assumption. Qed.
Print Assumptions registeredDecodeItemSavedFramePointerDecoder.

Lemma registeredDecodeItemStackEpilogueRestored (args : DecodeItemArgs) (frameBytes : list byte) (Hframe : decodeItemSavedFrameFacts args frameBytes) :
bv_add (Z_to_bv 64%N (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))
    (16%bv : bv 64%N) = Z_to_bv 64%N (decodeItemStackPointer args).
Proof. zesu_witness_facts. assumption. Qed.
Print Assumptions registeredDecodeItemStackEpilogueRestored.

Goal forall (args : DecodeItemArgs) (frameBytes : list byte),
Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  Z_to_bv 64%N (decodeItemReturnAddress args).
Proof. intros args frameBytes. Fail solve [zesu_witness_facts; assumption]. Abort.

Goal forall (args : DecodeItemArgs) (frameBytes : list byte),
Z_to_bv 64%N (little_endian_to_bv 8%N (take (N.to_nat 8%N) (drop
    (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 0 -
       (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))) =
  decodeItemSavedFramePointer args.
Proof. intros args frameBytes. Fail solve [zesu_witness_facts; assumption]. Abort.

