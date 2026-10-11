Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152_stageB_literal_shape (storage : list (bv 8)) :
 length storage = 40%nat ->
 SimplAnd (length (take 32 storage ++ bv_to_little_endian 8 8 4 ++ drop 40 storage) = 40%nat) True.
Proof.
intros Hstorage.
change (SimplAnd (length (take 32 storage ++
 (Z_to_bv 8 4) :: (Z_to_bv 8 0) :: (Z_to_bv 8 0) :: (Z_to_bv 8 0) ::
 (Z_to_bv 8 0) :: (Z_to_bv 8 0) :: (Z_to_bv 8 0) :: (Z_to_bv 8 0) ::
 drop 40 storage) = 40%nat) True).
typeclasses eauto.
Qed.
