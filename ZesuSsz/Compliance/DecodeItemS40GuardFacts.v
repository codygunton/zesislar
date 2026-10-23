Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemShortStringGuardRejected args (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  129 <= bv_unsigned inputPrefix <= 183 ->
  bv_unsigned prefix = bv_unsigned inputPrefix ->
  bv_signed (bv_zero_extend 128 (bv_and prefix 127)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hhead Hclass Hprefix Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hlength.
  assert (Hlen : 0 <= decodeItemInputLength args < word64Modulus) by
    (unfold word64Modulus; lia).
  pose proof (decodeItemShortStringMaskGuard prefix inputPrefix Hclass Hprefix) as Hmask.
  rewrite !zesu_signed_zero_extend_64_128 Hmask
    (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) in Hguard.
  eapply (decodeItemShortStringRejected args inputPrefix rest);
    [exact (proj2 Hdomain) | exact Hhead | exact Hclass |].
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  rewrite -Hinput Z.add_1_l.
  apply (proj2 (Z.lt_succ_r _ _)). exact (Z.ge_le _ _ Hguard).
Qed.

Lemma decodeItemShortStringGuardAccepted args (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  129 <= bv_unsigned inputPrefix <= 183 ->
  bv_unsigned prefix = bv_unsigned inputPrefix ->
  ~ bv_signed (bv_zero_extend 128 (bv_and prefix 127)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemAcceptedFacts args false 1 (bv_unsigned inputPrefix - 128).
Proof.
  intros Hdomain Hhead Hclass Hprefix Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hlength.
  assert (Hlen : 0 <= decodeItemInputLength args < word64Modulus) by
    (unfold word64Modulus; lia).
  pose proof (decodeItemShortStringMaskGuard prefix inputPrefix Hclass Hprefix) as Hmask.
  rewrite !zesu_signed_zero_extend_64_128 Hmask
    (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) in Hguard.
  eapply (decodeItemShortStringAccepted args inputPrefix rest);
    [exact (proj2 Hdomain) | exact Hhead | exact Hclass |].
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  rewrite -Hinput.
  apply Znot_ge_lt in Hguard.
  rewrite Z.add_1_l. apply Z.le_succ_l. exact Hguard.
Qed.

Lemma decodeItemSignedPrefixMask (prefix : byte) :
  bv_unsigned (bv_and (Z_to_bv 64 (bv_signed prefix)) 255) = bv_unsigned prefix.
Proof.
  rewrite bv_and_unsigned.
  change (Z.land (bv_unsigned (Z_to_bv 64 (bv_signed prefix))) (Z.ones 8) = bv_unsigned prefix).
  rewrite <- (bv_wrap_land 8 (bv_unsigned (Z_to_bv 64 (bv_signed prefix)))).
  rewrite Z_to_bv_unsigned bv_wrap_bv_wrap; last done.
  unfold bv_signed, bv_swrap. rewrite bv_wrap_sub_idemp_l.
  replace (bv_unsigned prefix + bv_half_modulus 8 - bv_half_modulus 8) with (bv_unsigned prefix) by ring.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma decodeItemMaskedEmptyStringAccepted args (prefix : byte) rest :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 = Z_to_bv 64 128 ->
  decodeItemAcceptedFacts args false 1 0.
Proof.
  intros Hdomain Hhead Hmask.
  pose proof (f_equal bv_unsigned Hmask) as Hprefix.
  rewrite decodeItemSignedPrefixMask in Hprefix.
  change (bv_unsigned prefix = 128) in Hprefix.
  exact (decodeItemEmptyAccepted args prefix rest (proj2 Hdomain) Hhead Hprefix).
Qed.

Lemma decodeItemOutputByte16Bound (storage : list byte) :
  length storage = 40%nat -> (16 < length storage)%nat.
Proof. intros Hlength. rewrite Hlength. lia. Qed.

Lemma decodeItemCompletedListFoldAlternateRejected args prefix rest n payloadStart bytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args true prefix rest n payloadStart bytes ->
  decodeItemByteFoldFacts args n n payloadStart bytes ->
  ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
    bv_signed (bv_zero_extend 128
      (Z_to_bv 64 (bigEndian (take (Z.to_nat n) bytes)) + Z_to_bv 64 (n + 1))) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hprovenance Hfold Hguard.
  apply Znot_ge_lt in Hguard.
  eapply decodeItemCompletedFoldRejected; [exact Hdomain | exact Hprovenance | exact Hfold |].
  exact (decodeItemCompletedFoldRejectGuard args n payloadStart bytes Hfold Hguard).
Qed.

#[export] Hint Extern 1 (SimplAnd (decodeItemAcceptedFacts ?args false 1
  (bv_unsigned ?prefix - 128)) True) =>
  match goal with
  | Hhead : decodeItemInputHead args prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix |- _ =>
    unfold SimplAnd; split;
    [intros _; eapply (decodeItemShortStringGuardAccepted args register prefix rest);
      solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix |- _ =>
    unfold SimplAnd; split;
    [intros _; eapply (decodeItemShortStringGuardRejected args register prefix rest);
      solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemShortStringGuardRejected.

Print Assumptions decodeItemShortStringGuardAccepted.

Print Assumptions decodeItemSignedPrefixMask.

Print Assumptions decodeItemOutputByte16Bound.

Print Assumptions decodeItemCompletedListFoldAlternateRejected.

Print Assumptions decodeItemMaskedEmptyStringAccepted.

Lemma decodeItemShortStringNegatedGuardUnsigned args (prefix : bv 64) :
  ~ bv_signed (bv_zero_extend 128 (bv_and prefix 127)) >=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  bv_unsigned (bv_and prefix 127) <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)).
Proof.
  intros Hguard. rewrite !zesu_signed_zero_extend_64_128 in Hguard.
  apply Znot_ge_lt in Hguard. exact Hguard.
Qed.

Print Assumptions decodeItemShortStringNegatedGuardUnsigned.

Lemma decodeItemNativeMaskConstant : (128%bv : bv 64) = Z_to_bv 64 128.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma decodeItemNativeMaskNonempty (prefix : byte) :
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv ->
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> Z_to_bv 64 128.
Proof. rewrite decodeItemNativeMaskConstant. trivial. Qed.

#[export] Hint Extern 1 (SimplAnd (129 <= bv_unsigned ?prefix) True) =>
  match goal with
  | Hlower : 128 <= bv_unsigned prefix,
    Hupper : bv_unsigned prefix <= 255,
    Hmask : bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemNonemptyStringPrefixGuard prefix
      (conj Hlower Hupper) (decodeItemNativeMaskNonempty prefix Hmask))
    | intros _; exact I]
  end : typeclass_instances.

Lemma decodeItemNativeMaskEmptyPrefix (prefix : byte) :
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 = 128%bv ->
  bv_unsigned prefix = 128.
Proof.
  intros Hmask. pose proof (f_equal bv_unsigned Hmask) as Hvalue.
  rewrite decodeItemSignedPrefixMask in Hvalue. exact Hvalue.
Qed.

Lemma decodeItemNativeMaskEmptyAccepted args (prefix : byte) rest :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 = 128%bv ->
  decodeItemAcceptedFacts args false 1 0.
Proof.
  intros Hdomain Hhead Hmask.
  apply (decodeItemMaskedEmptyStringAccepted args prefix rest Hdomain Hhead).
  rewrite <- decodeItemNativeMaskConstant. exact Hmask.
Qed.

Print Assumptions decodeItemNativeMaskConstant.
Print Assumptions decodeItemNativeMaskNonempty.
Print Assumptions decodeItemNativeMaskEmptyPrefix.
Print Assumptions decodeItemNativeMaskEmptyAccepted.
