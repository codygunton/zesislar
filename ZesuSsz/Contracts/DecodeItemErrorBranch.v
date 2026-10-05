From Coq Require Import Lia ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Open Scope Z_scope.

Lemma decodeItemErrorMaskedLengthGuard args (lengthRegister : bv 64) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  Z.land (bv_unsigned lengthRegister) 127 >= decodeItemInputLength args ->
  bv_unsigned (bv_and lengthRegister 127) >=
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)).
Proof.
  intros Hdomain Hguard.
  unfold decodeItemDomainAt, decodeItemC1BDomain,
    decodeItemArgsWellFormed in Hdomain.
  destruct Hdomain as [_ [_ [_ Hlayout]]].
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as (Hpointer & Hlength & Hnowrap & _).
  rewrite bv_and_unsigned.
  change (Z.land (bv_unsigned lengthRegister) 127 >=
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args))).
  rewrite Z_to_bv_small; [exact Hguard |].
  unfold word64Modulus in Hnowrap.
  unfold bv_modulus. lia.
Qed.

Lemma decodeItemErrorUnsignedComparison (x y : bv 64) :
  bv_unsigned x >= bv_unsigned y ->
  bv_signed (bv_zero_extend 128 x) >= bv_signed (bv_zero_extend 128 y).
Proof.
  intros Hguard.
  pose proof (bv_unsigned_in_range 64 x) as Hx.
  pose proof (bv_unsigned_in_range 64 y) as Hy.
  rewrite !bv_zero_extend_signed.
  rewrite !bv_swrap_small; try assumption;
    unfold bv_half_modulus, bv_modulus in *; lia.
Qed.

Definition decodeItemErrorBranchEntry `{!islaG Sigma} `{!threadG}
    args (frameBytes : list byte) (masked : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (x15 x16 : bv 64),
   ⌜decodeItemInputHead args inputPrefix rest /\
     129 <= bv_unsigned inputPrefix <= 183 /\
     bv_unsigned masked = bv_unsigned inputPrefix - 128 /\
     bv_unsigned masked >=
     bv_unsigned (Z_to_bv 64 (decodeItemInputLength args))⌝ ∗
   "x13" ↦ᵣ RVal_Bits masked ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 183) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   decodeItemBranchBase args frameBytes
     (Z_to_bv 64 (decodeItemInputPointer args)))%I.
