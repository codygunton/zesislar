Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemStackSubtraction args :
  (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv =
    Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes).
Proof. unfold RlpDecodeItem.decodeItemStackBytes. bv_solve. Qed.







Print Assumptions decodeItemStackSubtraction.
