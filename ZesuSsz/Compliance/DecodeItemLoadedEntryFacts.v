Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemEntryByteIndexFacts.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemLoadedEntryByte args prefix rest (loaded : byte) :
  decodeItemInputHead args prefix rest ->
  decodeItemInputBytes args !! 0%nat = Some loaded -> loaded = prefix.
Proof.
  intros Hhead Hlookup.
  pose proof (decodeItemEntryByteLookup args prefix rest Hhead) as Hprefix.
  rewrite Hprefix in Hlookup. congruence.
Qed.

Lemma decodeItemLoadedEntrySign args prefix rest (loaded : byte) :
  decodeItemInputHead args prefix rest ->
  decodeItemInputBytes args !! 0%nat = Some loaded ->
  bv_sign_extend 64 loaded = Z_to_bv 64 (bv_signed prefix).
Proof.
  intros Hhead Hlookup.
  rewrite (decodeItemLoadedEntryByte args prefix rest loaded Hhead Hlookup). bv_solve.
Qed.

Lemma decodeItemLoadedEntryNegative args prefix rest (loaded : byte) :
  decodeItemInputHead args prefix rest ->
  decodeItemInputBytes args !! 0%nat = Some loaded ->
  bv_signed (bv_sign_extend 128 (bv_sign_extend 64 loaded)) < bv_signed (0%bv : bv 128) ->
  128 <= bv_unsigned prefix.
Proof.
  intros Hhead Hlookup Hguard.
  rewrite (decodeItemLoadedEntryByte args prefix rest loaded Hhead Hlookup) in Hguard.
  rewrite !bv_sign_extend_signed in Hguard; try lia.
  pose proof (bv_unsigned_in_range 8 prefix) as Hrange.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hguard, Hrange.
  change ((bv_unsigned prefix + 128) mod 256 - 128 < 0) in Hguard.
  change (0 <= bv_unsigned prefix < 256) in Hrange.
  destruct (Z_le_gt_dec 128 (bv_unsigned prefix)); [assumption|].
  rewrite Z.mod_small in Hguard; lia.
Qed.

Lemma decodeItemLoadedEntryNonnegative args prefix rest (loaded : byte) :
  decodeItemInputHead args prefix rest ->
  decodeItemInputBytes args !! 0%nat = Some loaded ->
  ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 loaded)) < bv_signed (0%bv : bv 128) ->
  bv_unsigned prefix <= 127.
Proof.
  intros Hhead Hlookup Hguard.
  rewrite (decodeItemLoadedEntryByte args prefix rest loaded Hhead Hlookup) in Hguard.
  rewrite !bv_sign_extend_signed in Hguard; try lia.
  pose proof (bv_unsigned_in_range 8 prefix) as Hrange.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hguard, Hrange.
  change (~ (bv_unsigned prefix + 128) mod 256 - 128 < 0) in Hguard.
  change (0 <= bv_unsigned prefix < 256) in Hrange.
  destruct (Z_le_gt_dec (bv_unsigned prefix) 127); [assumption|].
  replace (bv_unsigned prefix + 128) with ((bv_unsigned prefix - 128) + 1 * 256) in Hguard; [|lia].
  rewrite Z.mod_add in Hguard; [|lia].
  rewrite Z.mod_small in Hguard; lia.
Qed.

Lemma decodeItemLoadedEntrySignedNegative (loaded : byte) :
  bv_signed (bv_sign_extend 128 (bv_sign_extend 64 loaded)) < bv_signed (0%bv : bv 128) ->
  bv_signed (bv_sign_extend 64 loaded) < 0.
Proof. rewrite !bv_sign_extend_signed; try lia. change (bv_signed loaded < 0 -> bv_signed loaded < 0). tauto. Qed.

Lemma decodeItemLoadedEntrySignedNonnegative (loaded : byte) :
  ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 loaded)) < bv_signed (0%bv : bv 128) ->
  0 <= bv_signed (bv_sign_extend 64 loaded).
Proof. rewrite !bv_sign_extend_signed; try lia. change (~ bv_signed loaded < 0 -> 0 <= bv_signed loaded). lia. Qed.

Lemma decodeItemLoadedEntryLiteral args prefix rest (loaded : byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  decodeItemInputBytes args !! 0%nat = Some loaded ->
  ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 loaded)) < bv_signed (0%bv : bv 128) ->
  decodeItemAcceptedFacts args false 0 1.
Proof.
  intros Hdomain Hhead Hlookup Hguard.
  apply (decodeItemLiteralAccepted args prefix rest (proj2 Hdomain) Hhead).
  exact (decodeItemLoadedEntryNonnegative args prefix rest loaded Hhead Hlookup Hguard).
Qed.

#[export] Hint Extern 1
  (SimplAnd (128 <= bv_unsigned ?prefix) True) =>
  match goal with
  | Hhead : decodeItemInputHead ?args ?prefix ?rest,
    Hlookup : decodeItemInputBytes ?args !! 0%nat = Some ?loaded,
    Hguard : bv_signed (bv_sign_extend 128 (bv_sign_extend 64 ?loaded)) < bv_signed (0%bv : bv 128) |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLoadedEntryNegative args prefix rest loaded Hhead Hlookup Hguard) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned ?prefix <= 127) True) =>
  match goal with
  | Hhead : decodeItemInputHead ?args ?prefix ?rest,
    Hlookup : decodeItemInputBytes ?args !! 0%nat = Some ?loaded,
    Hguard : ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 ?loaded)) < bv_signed (0%bv : bv 128) |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLoadedEntryNonnegative args prefix rest loaded Hhead Hlookup Hguard) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_sign_extend 64 ?loaded = Z_to_bv 64 (bv_signed ?prefix)) True) =>
  match goal with
  | Hhead : decodeItemInputHead ?args ?prefix ?rest,
    Hlookup : decodeItemInputBytes ?args !! 0%nat = Some loaded |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLoadedEntrySign args prefix rest loaded Hhead Hlookup) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_signed (bv_sign_extend 64 ?loaded) < 0) True) =>
  match goal with
  | Hguard : bv_signed (bv_sign_extend 128 (bv_sign_extend 64 ?loaded)) < bv_signed (0%bv : bv 128) |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLoadedEntrySignedNegative loaded Hguard) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (0 <= bv_signed (bv_sign_extend 64 ?loaded)) True) =>
  match goal with
  | Hguard : ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 ?loaded)) < bv_signed (0%bv : bv 128) |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLoadedEntrySignedNonnegative loaded Hguard) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemAcceptedFacts ?args false 0 1) True) =>
  match goal with
  | Hhead : decodeItemInputHead ?args ?prefix ?rest,
    Hlookup : decodeItemInputBytes ?args !! 0%nat = Some ?loaded,
    Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args,
    Hguard : ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 ?loaded)) < bv_signed (0%bv : bv 128) |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLoadedEntryLiteral args prefix rest loaded Hdomain Hhead Hlookup Hguard) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemLoadedEntryByte.

Print Assumptions decodeItemLoadedEntrySign.

Print Assumptions decodeItemLoadedEntryNegative.

Print Assumptions decodeItemLoadedEntryNonnegative.

Print Assumptions decodeItemLoadedEntrySignedNegative.

Print Assumptions decodeItemLoadedEntrySignedNonnegative.

Print Assumptions decodeItemLoadedEntryLiteral.
