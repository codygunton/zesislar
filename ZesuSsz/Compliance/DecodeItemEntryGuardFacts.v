Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemStackSubtraction args :
  (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv =
    Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes).
Proof. unfold RlpDecodeItem.decodeItemStackBytes. bv_solve. Qed.

Lemma decodeItemMaskedStringHeaderRejected args (register : bv 64)
    (prefix : byte) rest :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hhead Hclass Hvalue Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hbounds.
  assert (Hrange : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold bv_modulus; cbn; lia).
  rewrite !zesu_signed_zero_extend_64_128 in Hguard.
  pose proof (zesu_unsigned_low_mask_add_integer 64 8 register 255 73
    ltac:(done) ltac:(reflexivity)) as Hmask.
  rewrite Hmask (Z_to_bv_small 64 _ Hrange) in Hguard.
  exact (decodeItemLongStringHeaderGuardRejected args register prefix rest
    Hdomain Hhead Hclass Hvalue Hguard).
Qed.

Lemma decodeItemMaskedListHeaderRejected args (register : bv 64)
    (prefix : byte) rest :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hhead Hclass Hvalue Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hbounds.
  assert (Hrange : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold bv_modulus; cbn; lia).
  rewrite !zesu_signed_zero_extend_64_128 in Hguard.
  pose proof (zesu_unsigned_low_mask_add_integer 64 8 register 255 9
    ltac:(done) ltac:(reflexivity)) as Hmask.
  rewrite Hmask (Z_to_bv_small 64 _ Hrange) in Hguard.
  exact (decodeItemLongListHeaderGuardRejected args register prefix rest
    Hdomain Hhead Hclass Hvalue Hguard).
Qed.

#[export] Instance decodeItemStackSubtractionHint args :
  SimplAnd ((Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv =
    Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) True.
Proof.
  unfold SimplAnd; split;
    [intros _; apply decodeItemStackSubtraction | intros _; exact I].
Qed.

#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with
  | Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args,
    Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix,
    Hguard : bv_signed (bv_zero_extend 128 (bv_and (?register + 73) 255)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) |- _ =>
    unfold SimplAnd; split;
    [intros _; eapply (decodeItemMaskedStringHeaderRejected args register prefix rest);
      solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with
  | Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args,
    Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix,
    Hguard : bv_signed (bv_zero_extend 128 (bv_and (?register + 9) 255)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) |- _ =>
    unfold SimplAnd; split;
    [intros _; eapply (decodeItemMaskedListHeaderRejected args register prefix rest);
      solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemStackSubtraction.
Print Assumptions decodeItemMaskedStringHeaderRejected.
Print Assumptions decodeItemMaskedListHeaderRejected.
Print Assumptions decodeItemStackSubtractionHint.
