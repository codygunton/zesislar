Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Lemma decodeItemListLookupNthError {A : Type} (bytes : list A) index :
  nth_error bytes index = bytes !! index.
Proof.
  revert bytes. induction index as [|index IH]; intros [|head tail]; cbn; try reflexivity.
  apply IH.
Qed.

Lemma decodeItemFoldExitIndex args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  0 <= decodeItemInputPointer args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv = Z_to_bv 64 (payloadStart + n) ->
  i + 1 = n.
Proof.
  intros (Hwidth & Hi & Hstart & Hbytes & Hlength & Hfit) Hguard Hp Hnowrap Heq.
  assert (Hnext : 0 <= payloadStart + i + 1 < bv_modulus 64).
  { unfold word64Modulus, bv_modulus in *; cbn in *; lia. }
  assert (Hend : 0 <= payloadStart + n < bv_modulus 64).
  { unfold word64Modulus, bv_modulus in *; cbn in *; lia. }
  replace (Z_to_bv 64 (payloadStart + i) + 1)%bv with
    (Z_to_bv 64 (payloadStart + i + 1)) in Heq by bv_solve.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (Z_to_bv_small 64 _ Hnext) (Z_to_bv_small 64 _ Hend) in Heq. lia.
Qed.

Lemma decodeItemFoldExitAccumulator args n i payloadStart bytes next :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  0 <= decodeItemInputPointer args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv = Z_to_bv 64 (payloadStart + n) ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
    (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes)).
Proof.
  intros Hfold Hguard Hp Hnowrap Heq Hlookup.
  rewrite -decodeItemListLookupNthError in Hlookup.
  pose proof (decodeItemFoldExitIndex args n i payloadStart bytes Hfold Hguard Hp Hnowrap Heq) as Hindex.
  rewrite -Hindex. apply (decodeItemFoldSteppedAccumulator args n i payloadStart bytes next Hfold Hguard Hlookup).
Qed.

Lemma decodeItemFoldInputBaseGuardImpossible args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  decodeItemC1BDomain args ->
  bv_zero_extend 128 ((Z_to_bv 64 (payloadStart + i) + 0)%bv) = 1073741824%bv -> False.
Proof.
intros (Hwidth & Hi & Hstart & Hbytes & HbytesLength & Hfit) Hguard (Hlength & Hstorage & Hlayout) Heq.
unfold decodeItemEntryLayout in Hlayout.
destruct Hlayout as (Hp & Hl & Hnowrap & Ho & Hon & Hstack & Hslo & Hshi & HsepIO & HsepIS & HsepOS & Hret & Halign & Hreadable & Hrest).
assert (Hmin : 1073741824 <= decodeItemInputPointer args).
{
cbn [mapInputBufferAddress mapRamBase defaultMap] in Hreadable.
destruct Hreadable as [[Hmin _] | [Hmin _]]; lia.
}
assert (Hcursor : 0 <= payloadStart + i < bv_modulus 64).
{
unfold word64Modulus, bv_modulus in *; cbn in *; lia.
}
apply (f_equal bv_unsigned) in Heq.
revert Heq.
bv_simplify.
rewrite Z.add_0_r.
rewrite (bv_wrap_small 64 _ Hcursor).
lia.
Qed.

#[export] Hint Extern 1 (SimplAnd ?P True) =>
  match goal with
  | Hfold : decodeItemByteFoldFacts ?args ?n ?i ?payloadStart ?bytes,
    Hguard : ?i < ?n,
    Hdomain : decodeItemDomainAt (decodeItemReturnAddress ?args) decodeItemC1BDomain ?args,
    Hmetadata : bv_zero_extend 128 ((Z_to_bv 64 (?payloadStart + ?i) + 0)%bv) = 1073741824%bv |- _ =>
    unfold SimplAnd; split;
    [intros _; exfalso; exact (decodeItemFoldInputBaseGuardImpossible args n i payloadStart bytes
      Hfold Hguard (proj2 Hdomain) Hmetadata) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemFoldExitIndex.
Print Assumptions decodeItemFoldExitAccumulator.
Print Assumptions decodeItemFoldInputBaseGuardImpossible.

Print Assumptions decodeItemListLookupNthError.
