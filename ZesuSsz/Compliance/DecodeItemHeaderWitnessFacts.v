Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemDataWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldRejectionFacts.
Require Import ZesuSsz.Compliance.DecodeItemEntryGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemInputHeadWordFacts.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemInputHeadWitnessFacts returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
  exists prefix rest, decodeItemInputHead args prefix rest.
Proof. exact (decodeItemDomainNonemptyInputHead returnAddress args). Qed.

Lemma decodeItemStringHeaderProvenanceFacts args prefix rest :
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183)
    (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest).
Proof. intros Hhead Hclass. unfold decodeItemFoldProvenance. simpl. tauto. Qed.

Lemma decodeItemListHeaderProvenanceFacts args prefix rest :
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247)
    (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest).
Proof. intros Hhead Hclass. unfold decodeItemFoldProvenance. simpl. tauto. Qed.

Lemma decodeItemHeaderInitialFoldFacts returnAddress args prefix rest n :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  1 <= n <= 8 -> n < decodeItemInputLength args ->
  decodeItemByteFoldFacts args n 0 (decodeItemInputPointer args + 1)
    (firstn (Z.to_nat n) rest).
Proof.
  intros Hdomain Hhead Hwidth Hfits.
  destruct (proj2 Hdomain) as (Hlength & Hstorage & Hlayout).
  unfold decodeItemInputHead in Hhead. rewrite Hhead in Hlength. simpl in Hlength.
  unfold decodeItemByteFoldFacts. rewrite Hhead. simpl.
  repeat split; try lia; try reflexivity.
  rewrite firstn_length Nat.min_l; [rewrite Z2Nat.id; lia | lia].
Qed.

Lemma decodeItemStringHeaderReadGuardFacts args (register : bv 64) (prefix : byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  ~ bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  bv_unsigned prefix - 183 < decodeItemInputLength args.
Proof.
  intros Hdomain Hclass Hvalue Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hlength.
  assert (Hlen : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold bv_modulus; simpl; lia).
  assert (Hmask : bv_unsigned (bv_and (register + 73) 255) = bv_unsigned prefix - 183).
  { pose proof (zesu_unsigned_low_mask_add_integer 64 8 register 255 73
      ltac:(done) ltac:(reflexivity)) as Hlow.
    rewrite Hlow Hvalue Z_to_bv_unsigned.
    change ((bv_unsigned prefix + 73) mod 256 = bv_unsigned prefix - 183).
    replace (bv_unsigned prefix + 73) with ((bv_unsigned prefix - 183) + 1 * 256) by ring.
    rewrite Z.mod_add; [apply Z.mod_small; lia | lia]. }
  rewrite !zesu_signed_zero_extend_64_128 Hmask
    (Z_to_bv_small 64 _ Hlen) in Hguard.
  apply Znot_ge_lt in Hguard. exact Hguard.
Qed.

Lemma decodeItemListHeaderReadGuardFacts args (register : bv 64) (prefix : byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  ~ bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  bv_unsigned prefix - 247 < decodeItemInputLength args.
Proof.
  intros Hdomain Hclass Hvalue Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hlength.
  assert (Hlen : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold bv_modulus; simpl; lia).
  assert (Hmask : bv_unsigned (bv_and (register + 9) 255) = bv_unsigned prefix - 247).
  { pose proof (zesu_unsigned_low_mask_add_integer 64 8 register 255 9
      ltac:(done) ltac:(reflexivity)) as Hlow.
    rewrite Hlow Hvalue Z_to_bv_unsigned.
    change ((bv_unsigned prefix + 9) mod 256 = bv_unsigned prefix - 247).
    replace (bv_unsigned prefix + 9) with ((bv_unsigned prefix - 247) + 1 * 256) by ring.
    rewrite Z.mod_add; [apply Z.mod_small; lia | lia]. }
  rewrite !zesu_signed_zero_extend_64_128 Hmask
    (Z_to_bv_small 64 _ Hlen) in Hguard.
  apply Znot_ge_lt in Hguard. exact Hguard.
Qed.

Lemma decodeItemHeaderUnsignedReadGuardFacts returnAddress args n :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  0 <= n -> n < decodeItemInputLength args ->
  bv_unsigned (Z_to_bv 64 n) <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)).
Proof.
  intros Hdomain Hnonnegative Hfits.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hlength.
  assert (Hlen : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold bv_modulus; simpl; lia).
  assert (Hn : 0 <= n < bv_modulus 64) by lia.
  rewrite (Z_to_bv_small 64 _ Hn) (Z_to_bv_small 64 _ Hlen). exact Hfits.
Qed.

Lemma decodeItemCompletedFoldAcceptedWitnessFacts args isList prefix rest n payloadStart lengthBytes :
  decodeItemC1BDomain args ->
  decodeItemFoldProvenance args isList prefix rest n payloadStart lengthBytes ->
  decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
  decodeItemFoldLengthFits args n lengthBytes = true ->
  decodeItemLongAcceptedFacts args isList (1 + n) (bigEndian lengthBytes).
Proof.
  intros Hdomain Hprovenance Hfold Hfits.
  pose proof (decodeItemDomainInputLengthBounds args Hdomain) as Hbounds.
  assert (Hrange : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold bv_modulus; simpl; lia).
  pose proof Hdomain as Hfacts. destruct Hfacts as (Hinput & Hstorage & Hlayout).
  eapply (decodeItemLongAccepted args isList prefix rest n payloadStart lengthBytes);
    [exact Hdomain | exact Hprovenance | |].
  - unfold decodeItemByteFoldFacts in Hfold. rewrite -Hinput. lia.
  - unfold decodeItemFoldLengthFits in Hfits. apply Z.leb_le in Hfits.
    rewrite (Z_to_bv_small 64 _ Hrange) Z_to_bv_unsigned in Hfits.
    rewrite -Hinput. unfold word64Modulus.
    replace (1 + n + bigEndian lengthBytes) with (bigEndian lengthBytes + n + 1) by ring.
    exact Hfits.
Qed.

Lemma decodeItemCompletedFoldConsumedWord args n payloadStart lengthBytes :
  decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
  Z_to_bv 64 (bigEndian lengthBytes + n + 1) =
    (Z_to_bv 64 (bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n + 1))%bv.
Proof.
  intros Hfold.
  assert (Htake : take (Z.to_nat n) lengthBytes = lengthBytes).
  { unfold decodeItemByteFoldFacts in Hfold.
    destruct Hfold as (Hwidth & Hi & Hstart & Hbytes & Hlength & Hfits).
    apply firstn_all2. lia. }
  rewrite Htake.
  replace (bigEndian lengthBytes + n + 1) with (bigEndian lengthBytes + (n + 1)) by ring.
  bv_solve.
Qed.

Lemma decodeItemCompletedFoldFitsGuard args n payloadStart lengthBytes :
  decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
  ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed (bv_zero_extend 128
      (Z_to_bv 64 (bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n + 1))) ->
  decodeItemFoldLengthFits args n lengthBytes = true.
Proof.
  intros Hfold Hguard. unfold decodeItemFoldLengthFits. apply Z.leb_le.
  rewrite (decodeItemCompletedFoldConsumedWord args n payloadStart lengthBytes Hfold).
  rewrite !zesu_signed_zero_extend_64_128 in Hguard. lia.
Qed.

Lemma decodeItemCompletedFoldRejectGuard args n payloadStart lengthBytes :
  decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
  bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed (bv_zero_extend 128
      (Z_to_bv 64 (bigEndian (take (Z.to_nat n) lengthBytes)) + Z_to_bv 64 (n + 1))) ->
  decodeItemFoldLengthFits args n lengthBytes = false.
Proof.
  intros Hfold Hguard. unfold decodeItemFoldLengthFits. apply Z.leb_gt.
  rewrite (decodeItemCompletedFoldConsumedWord args n payloadStart lengthBytes Hfold).
  rewrite !zesu_signed_zero_extend_64_128 in Hguard. lia.
Qed.

Lemma decodeItemInputPointerCastWitnessFacts returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = decodeItemInputPointer args.
Proof.
  intros Hdomain. destruct (proj2 Hdomain) as (Hinput & Hstorage & Hlayout).
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as (Hpointer & Hlength & Hnowrap & Hrest).
  assert (Hrange : 0 <= decodeItemInputPointer args < bv_modulus 64) by
    (unfold word64Modulus in *; change (0 <= decodeItemInputPointer args < 2^64); lia).
  exact (Z_to_bv_small 64 _ Hrange).
Qed.

#[export] Hint Extern 1 (SimplAnd (decodeItemC1BDomain ?args) True) =>
  match goal with Hdomain : decodeItemDomainAt ?returnAddress decodeItemC1BDomain args |- _ =>
    unfold SimplAnd; split; [intros _; exact (proj2 Hdomain) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (exists prefix rest, decodeItemInputHead ?args prefix rest) True) =>
  match goal with
  | Hdomain : decodeItemDomainAt ?returnAddress decodeItemC1BDomain args,
    Hnonzero : bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemInputHeadWitnessFacts returnAddress args Hdomain Hnonzero)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (1 <= bv_unsigned ?prefix - 183 <= 8) True) =>
  match goal with Hlow : 184 <= bv_unsigned prefix, Hhigh : bv_unsigned prefix <= 191 |- _ =>
    unfold SimplAnd; split;
    [intros _; apply decodeItemLongStringHeaderWidth; split; assumption | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (1 <= bv_unsigned ?prefix - 247 <= 8) True) =>
  match goal with Hlow : 248 <= bv_unsigned prefix, Hhigh : bv_unsigned prefix <= 255 |- _ =>
    unfold SimplAnd; split;
    [intros _; apply decodeItemLongListHeaderWidth; split; assumption | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemFoldProvenance ?args false ?prefix ?rest
    (bv_unsigned ?prefix - 183) (decodeItemInputPointer ?args + 1)
    (firstn (Z.to_nat (bv_unsigned ?prefix - 183)) ?rest)) True) =>
  unfold SimplAnd; split;
  [intros _; apply decodeItemStringHeaderProvenanceFacts;
    solve [eassumption | split; assumption] | intros _; exact I]
  : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemFoldProvenance ?args true ?prefix ?rest
    (bv_unsigned ?prefix - 247) (decodeItemInputPointer ?args + 1)
    (firstn (Z.to_nat (bv_unsigned ?prefix - 247)) ?rest)) True) =>
  unfold SimplAnd; split;
  [intros _; apply decodeItemListHeaderProvenanceFacts;
    solve [eassumption | split; assumption] | intros _; exact I]
  : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned ?prefix - 183 < decodeItemInputLength ?args) True) =>
  match goal with Hvalue : bv_unsigned ?register = bv_unsigned prefix |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemStringHeaderReadGuardFacts args register prefix);
      solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned ?prefix - 247 < decodeItemInputLength ?args) True) =>
  match goal with Hvalue : bv_unsigned ?register = bv_unsigned prefix |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemListHeaderReadGuardFacts args register prefix);
      solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemByteFoldFacts ?args ?n 0 (decodeItemInputPointer ?args + 1)
    (firstn (Z.to_nat ?n) ?rest)) True) =>
  assert_fails (has_evar n);
  match goal with Hhead : decodeItemInputHead args ?prefix rest,
    Hdomain : decodeItemDomainAt ?returnAddress decodeItemC1BDomain args |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemHeaderInitialFoldFacts returnAddress args prefix rest n);
      [exact Hdomain | exact Hhead |
        let Hwidth := constr:(_ : SimplAnd (1 <= n <= 8) True) in exact ((proj1 Hwidth) I) |
        let Hfits := constr:(_ : SimplAnd (n < decodeItemInputLength args) True) in exact ((proj1 Hfits) I)]
    | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemInputHeadWitnessFacts.
Print Assumptions decodeItemStringHeaderProvenanceFacts.
Print Assumptions decodeItemListHeaderProvenanceFacts.
Print Assumptions decodeItemHeaderInitialFoldFacts.
Print Assumptions decodeItemStringHeaderReadGuardFacts.
Print Assumptions decodeItemListHeaderReadGuardFacts.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned (Z_to_bv 64 ?n) <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength ?args))) True) =>
  assert_fails (has_evar n);
  match goal with Hdomain : decodeItemDomainAt ?returnAddress decodeItemC1BDomain args |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemHeaderUnsignedReadGuardFacts returnAddress args n);
      [exact Hdomain |
        let Hwidth := constr:(_ : SimplAnd (1 <= n <= 8) True) in
        pose proof ((proj1 Hwidth) I); lia |
        let Hfits := constr:(_ : SimplAnd (n < decodeItemInputLength args) True) in exact ((proj1 Hfits) I)]
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemLongAcceptedFacts ?args ?isList (1 + ?n) (bigEndian ?lengthBytes)) True) =>
  match goal with
  | Hdomain : decodeItemC1BDomain args,
    Hprovenance : decodeItemFoldProvenance args isList ?prefix ?rest n ?payloadStart lengthBytes,
    Hfold : decodeItemByteFoldFacts args n n ?payloadStart lengthBytes,
    Hfits : decodeItemFoldLengthFits args n lengthBytes = true |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemCompletedFoldAcceptedWitnessFacts args isList prefix rest n
      payloadStart lengthBytes Hdomain Hprovenance Hfold Hfits) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemHeaderUnsignedReadGuardFacts.
Print Assumptions decodeItemCompletedFoldAcceptedWitnessFacts.

#[export] Hint Extern 1 (SimplAnd (decodeItemFoldLengthFits ?args ?n ?lengthBytes = true) True) =>
  match goal with Hfold : decodeItemByteFoldFacts args n n ?payloadStart lengthBytes |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemCompletedFoldFitsGuard args n payloadStart lengthBytes Hfold); assumption
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (decodeItemFoldLengthFits ?args ?n ?lengthBytes = false) True) =>
  match goal with Hfold : decodeItemByteFoldFacts args n n ?payloadStart lengthBytes |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemCompletedFoldRejectGuard args n payloadStart lengthBytes Hfold); assumption
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with
  | Hdomain : decodeItemC1BDomain args,
    Hprovenance : decodeItemFoldProvenance args ?isList ?prefix ?rest ?n ?payloadStart ?lengthBytes,
    Hfold : decodeItemByteFoldFacts args ?n ?n ?payloadStart ?lengthBytes |- _ =>
    let Hfits := constr:(_ : SimplAnd (decodeItemFoldLengthFits args n lengthBytes = false) True) in
    unfold SimplAnd; split;
    [intros _; exact (decodeItemCompletedFoldRejected args isList prefix rest n payloadStart lengthBytes
      Hdomain Hprovenance Hfold ((proj1 Hfits) I)) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemLongAcceptedFacts ?args ?isList (1 + ?n) (bigEndian ?lengthBytes)) True) =>
  match goal with
  | Hdomain : decodeItemC1BDomain args,
    Hprovenance : decodeItemFoldProvenance args isList ?prefix ?rest n ?payloadStart lengthBytes,
    Hfold : decodeItemByteFoldFacts args n n ?payloadStart lengthBytes |- _ =>
    let Hfits := constr:(_ : SimplAnd (decodeItemFoldLengthFits args n lengthBytes = true) True) in
    unfold SimplAnd; split;
    [intros _; exact (decodeItemCompletedFoldAcceptedWitnessFacts args isList prefix rest n
      payloadStart lengthBytes Hdomain Hprovenance Hfold ((proj1 Hfits) I)) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemCompletedFoldConsumedWord.
Print Assumptions decodeItemCompletedFoldFitsGuard.
Print Assumptions decodeItemCompletedFoldRejectGuard.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer ?args)) = decodeItemInputPointer ?args) True) =>
  match goal with Hdomain : decodeItemDomainAt ?returnAddress decodeItemC1BDomain args |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemInputPointerCastWitnessFacts returnAddress args Hdomain)
    | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemInputPointerCastWitnessFacts.
