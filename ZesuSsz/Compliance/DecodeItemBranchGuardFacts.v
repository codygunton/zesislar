Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.LowMask.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Open Scope Z_scope.

Lemma decodeItemShortListGuardRejected args (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  192 <= bv_unsigned inputPrefix <= 247 ->
  bv_unsigned prefix = bv_unsigned inputPrefix ->
  bv_signed (bv_zero_extend 128 (bv_and (prefix + 64) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hhead Hclass Hprefix Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hlength.
  assert (Hlen : 0 <= decodeItemInputLength args < word64Modulus) by
    (unfold word64Modulus; lia).
  assert (Hmask : bv_unsigned (bv_and (prefix + 64) 255) =
    bv_unsigned inputPrefix - 192).
  { pose proof (zesu_unsigned_low_mask_add_integer 64 8 prefix 255 64
      ltac:(done) ltac:(reflexivity)) as Hlow.
    rewrite Hlow Hprefix Z_to_bv_unsigned.
    change ((bv_unsigned inputPrefix + 64) mod 256 = bv_unsigned inputPrefix - 192).
    replace (bv_unsigned inputPrefix + 64) with
      ((bv_unsigned inputPrefix - 192) + 1 * 256) by ring.
    rewrite Z.mod_add; [apply Z.mod_small; lia | lia]. }
  rewrite !zesu_signed_zero_extend_64_128 Hmask
    (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) in Hguard.
  eapply (decodeItemShortListRejected args inputPrefix rest);
    [exact (proj2 Hdomain) | exact Hhead | exact Hclass |].
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  rewrite -Hinput Z.add_1_l.
  apply (proj2 (Z.lt_succ_r _ _)). exact (Z.ge_le _ _ Hguard).
Qed.

Lemma decodeItemShortListGuardAccepted args (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  192 <= bv_unsigned inputPrefix <= 247 ->
  bv_unsigned prefix = bv_unsigned inputPrefix ->
  ~ bv_signed (bv_zero_extend 128 (bv_and (prefix + 64) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemAcceptedFacts args true 1 (bv_unsigned inputPrefix - 192).
Proof.
  intros Hdomain Hhead Hclass Hprefix Hguard.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hdomain)) as Hlength.
  assert (Hlen : 0 <= decodeItemInputLength args < word64Modulus) by
    (unfold word64Modulus; lia).
  assert (Hmask : bv_unsigned (bv_and (prefix + 64) 255) =
    bv_unsigned inputPrefix - 192).
  { pose proof (zesu_unsigned_low_mask_add_integer 64 8 prefix 255 64
      ltac:(done) ltac:(reflexivity)) as Hlow.
    rewrite Hlow Hprefix Z_to_bv_unsigned.
    change ((bv_unsigned inputPrefix + 64) mod 256 = bv_unsigned inputPrefix - 192).
    replace (bv_unsigned inputPrefix + 64) with
      ((bv_unsigned inputPrefix - 192) + 1 * 256) by ring.
    rewrite Z.mod_add; [apply Z.mod_small; lia | lia]. }
  rewrite !zesu_signed_zero_extend_64_128 Hmask
    (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) in Hguard.
  eapply (decodeItemShortListAccepted args inputPrefix rest);
    [exact (proj2 Hdomain) | exact Hhead | exact Hclass |].
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  rewrite -Hinput.
  apply Znot_ge_lt in Hguard.
  rewrite Z.add_1_l. apply Z.le_succ_l. exact Hguard.
Qed.

Lemma decodeItemNonemptyInputByteBound args :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
  bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args) + 0) + 1) <=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputEnd args))).
Proof.
  intros Hdomain Hnonzero.
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as
    (Hpointer & Hlength & Hnowrap & Houtput & HoutputEnd &
     Hstack & HstackBase & HstackEnd & Hseparation1 & Hseparation2 &
     Hseparation3 & Hreturn & Halignment & Hreadable & HoutputBase &
     HoutputBound & Hend & Hslice).
  assert (Hlen : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold word64Modulus in *; change (0 <= decodeItemInputLength args < 2^64); lia).
  rewrite (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) in Hnonzero.
  replace (Z_to_bv 64 (decodeItemInputPointer args) + 0)%bv with
    (Z_to_bv 64 (decodeItemInputPointer args)) by bv_solve.
  rewrite (zesu_signed_zero_extend_add_64_128
    (Z_to_bv 64 (decodeItemInputPointer args)) 1 ltac:(done)).
  rewrite zesu_signed_zero_extend_64_128.
  assert (Hptr : 0 <= decodeItemInputPointer args < bv_modulus 64) by
    (unfold word64Modulus in *; change (0 <= decodeItemInputPointer args < 2^64); lia).
  assert (Hend64 : 0 <= decodeItemInputEnd args < bv_modulus 64) by exact Hend.
  rewrite (Z_to_bv_small 64 _ Hptr) (Z_to_bv_small 64 _ Hend64).
  change (decodeItemInputPointer args + 1 <= decodeItemInputEnd args). lia.
Qed.

#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix |- _ =>
    unfold SimplAnd; split; [intros _;
      eapply (decodeItemShortListGuardRejected args register prefix rest);
        solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemAcceptedFacts ?args true 1 _) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix |- _ =>
    unfold SimplAnd; split; [intros _;
      eapply (decodeItemShortListGuardAccepted args register prefix rest);
        solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd ?P True) =>
  match goal with
  | Hdomain : decodeItemDomainAt (decodeItemReturnAddress ?args) decodeItemC1BDomain ?args,
    Hnonzero : bv_unsigned (Z_to_bv 64 (decodeItemInputLength ?args)) <> 0,
    Hfault : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer ?args) + 0) + 1) <=
      bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputEnd ?args))) |- _ =>
    let Hbound := constr:(decodeItemNonemptyInputByteBound args Hdomain Hnonzero) in
    unfold SimplAnd; split; [intros _; exfalso; exact (Hfault Hbound) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemShortListGuardRejected.
Print Assumptions decodeItemShortListGuardAccepted.
Print Assumptions decodeItemNonemptyInputByteBound.

Lemma decodeItemNonemptyInputReadableBounds args :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
  decodeItemInputPointer args + 1 <= 0xc0000000 /\
  (decodeItemInputPointer args < 0xa0000000 ->
    decodeItemInputPointer args + 1 <= 0x80000000).
Proof.
  intros Hdomain Hnonzero.
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as
    (Hpointer & Hlength & Hnowrap & Houtput & HoutputEnd &
     Hstack & HstackBase & HstackEnd & Hseparation1 & Hseparation2 &
     Hseparation3 & Hreturn & Halignment & Hreadable & HoutputBase &
     HoutputBound & Hend & Hslice).
  assert (Hlen : 0 <= decodeItemInputLength args < bv_modulus 64) by
    (unfold word64Modulus in *; change (0 <= decodeItemInputLength args < 2^64); lia).
  rewrite (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) in Hnonzero.
  cbv [mapInputBufferAddress mapInputCapacity mapRamBase machineRamEnd
    mapRamSize defaultMap] in Hreadable.
  destruct Hreadable as [[Hbase Hbound] | [Hbase Hbound]]; split; lia.
Qed.

Lemma decodeItemNonemptyInputPhysicalByteBounds args :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
  bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args) + 0) + 1) <=
    bv_signed (Z_to_bv 128 0xc0000000) /\
  (~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args) + 0)) >=
    bv_signed (Z_to_bv 128 0xa0000000) ->
   bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args) + 0) + 1) <=
    bv_signed (Z_to_bv 128 0x80000000)).
Proof.
  intros Hdomain Hnonzero.
  pose proof (decodeItemNonemptyInputReadableBounds args Hdomain Hnonzero) as Hbounds.
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as (Hpointer & Hlength & Hnowrap & Hrest).
  assert (Hptr : 0 <= decodeItemInputPointer args < bv_modulus 64) by
    (unfold word64Modulus in *; change (0 <= decodeItemInputPointer args < 2^64); lia).
  replace (Z_to_bv 64 (decodeItemInputPointer args) + 0)%bv with
    (Z_to_bv 64 (decodeItemInputPointer args)) by bv_solve.
  rewrite !zesu_signed_zero_extend_add_64_128; try done.
  rewrite !zesu_signed_zero_extend_64_128 (Z_to_bv_small 64 _ Hptr).
  change (decodeItemInputPointer args + 1 <= 0xc0000000 /\
    (~ decodeItemInputPointer args >= 0xa0000000 ->
     decodeItemInputPointer args + 1 <= 0x80000000)).
  destruct Hbounds as [Hram HinputBound]. split; [exact Hram | intros Hlow; apply HinputBound; lia].
Qed.

#[export] Hint Extern 1 (SimplAnd ?P True) =>
  match goal with
  | Hdomain : decodeItemDomainAt (decodeItemReturnAddress ?args) decodeItemC1BDomain ?args,
    Hnonzero : bv_unsigned (Z_to_bv 64 (decodeItemInputLength ?args)) <> 0,
    Hfault : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer ?args) + 0) + 1) <=
      bv_signed (Z_to_bv 128 0xc0000000) |- _ =>
    let Hbound := constr:(proj1 (decodeItemNonemptyInputPhysicalByteBounds args Hdomain Hnonzero)) in
    unfold SimplAnd; split; [intros _; exfalso; exact (Hfault Hbound) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd ?P True) =>
  match goal with
  | Hdomain : decodeItemDomainAt (decodeItemReturnAddress ?args) decodeItemC1BDomain ?args,
    Hnonzero : bv_unsigned (Z_to_bv 64 (decodeItemInputLength ?args)) <> 0,
    Hlower : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer ?args) + 0)) >=
      bv_signed (Z_to_bv 128 0xa0000000),
    Hfault : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer ?args) + 0) + 1) <=
      bv_signed (Z_to_bv 128 0x80000000) |- _ =>
    let Hbound := constr:(proj2 (decodeItemNonemptyInputPhysicalByteBounds args Hdomain Hnonzero) Hlower) in
    unfold SimplAnd; split; [intros _; exfalso; exact (Hfault Hbound) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemNonemptyInputReadableBounds.
Print Assumptions decodeItemNonemptyInputPhysicalByteBounds.

Lemma decodeItemLongStringHeaderGuardRejected args (register : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  184 <= bv_unsigned inputPrefix <= 191 ->
  bv_unsigned register = bv_unsigned inputPrefix ->
  bv_unsigned (Z_to_bv 8 (bv_unsigned register + 73)) >=
    decodeItemInputLength args ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hhead Hclass Hvalue Hguard.
  assert (Hheader : bv_unsigned (Z_to_bv 8 (bv_unsigned register + 73)) =
    bv_unsigned inputPrefix - 183) by bv_solve.
  rewrite Hheader in Hguard.
  eapply (decodeItemLongStringHeaderRejected args inputPrefix rest);
    [exact (proj2 Hdomain) | exact Hhead | exact Hclass |].
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  rewrite -Hinput Z.add_1_l.
  apply (proj2 (Z.lt_succ_r _ _)). exact (Z.ge_le _ _ Hguard).
Qed.

#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix |- _ =>
    unfold SimplAnd; split; [intros _;
      eapply (decodeItemLongStringHeaderGuardRejected args register prefix rest);
        solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemLongStringHeaderGuardRejected.

Lemma decodeItemLongListHeaderGuardRejected args (register : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args inputPrefix rest ->
  248 <= bv_unsigned inputPrefix <= 255 ->
  bv_unsigned register = bv_unsigned inputPrefix ->
  bv_unsigned (Z_to_bv 8 (bv_unsigned register + 9)) >=
    decodeItemInputLength args ->
  decodeItemRejectedFacts args.
Proof.
  intros Hdomain Hhead Hclass Hvalue Hguard.
  assert (Hheader : bv_unsigned (Z_to_bv 8 (bv_unsigned register + 9)) =
    bv_unsigned inputPrefix - 247) by bv_solve.
  rewrite Hheader in Hguard.
  eapply (decodeItemLongListHeaderRejected args inputPrefix rest);
    [exact (proj2 Hdomain) | exact Hhead | exact Hclass |].
  destruct (proj2 Hdomain) as [Hinput [Hstorage Hlayout]].
  rewrite -Hinput Z.add_1_l.
  apply (proj2 (Z.lt_succ_r _ _)). exact (Z.ge_le _ _ Hguard).
Qed.

#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix |- _ =>
    unfold SimplAnd; split; [intros _;
      eapply (decodeItemLongListHeaderGuardRejected args register prefix rest);
        solve [eassumption | split; assumption] | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemLongListHeaderGuardRejected.
