Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Open Scope Z_scope.

Ltac entry_guard_registered :=
  lazymatch goal with |- ?P =>
    let evidence := constr:(_ : SimplAnd P True) in exact (proj1 evidence I)
  end.

Ltac entry_guard_absent args :=
  let target := constr:(SimplAnd (decodeItemRejectedFacts args) True) in
  assert_fails (assert target by typeclasses eauto); exact I.
Lemma entryStackOff (args : DecodeItemArgs) : True.
Proof.
  let target := constr:(SimplAnd
    ((Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv =
      Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)) True) in
  assert_fails (assert target by typeclasses eauto). exact I.
Qed.

Lemma entryStringOff (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryListOff (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Require Import ZesuSsz.Compliance.DecodeItemEntryGuardFacts.

Lemma entryStackOn args :
  (Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv =
    Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes).
Proof. entry_guard_registered. Qed.

Lemma entryStringOn (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemRejectedFacts args.
Proof. intros. entry_guard_registered. Qed.

Lemma entryStringMissingDomain (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryStringMissingClass (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryStringMissingValue (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryStringMissingGuard (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryStringWrongMask (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 256)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryListOn (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  decodeItemRejectedFacts args.
Proof. intros. entry_guard_registered. Qed.

Lemma entryListMissingDomain (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryListMissingClass (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryListMissingValue (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryListMissingGuard (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Lemma entryListWrongMask (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 256)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  True.
Proof. intros. entry_guard_absent args. Qed.

Print Assumptions entryStackOff.
Print Assumptions entryStringOff.
Print Assumptions entryListOff.
Print Assumptions entryStackOn.
Print Assumptions entryStringOn.
Print Assumptions entryStringMissingDomain.
Print Assumptions entryStringMissingClass.
Print Assumptions entryStringMissingValue.
Print Assumptions entryStringMissingGuard.
Print Assumptions entryStringWrongMask.
Print Assumptions entryListOn.
Print Assumptions entryListMissingDomain.
Print Assumptions entryListMissingClass.
Print Assumptions entryListMissingValue.
Print Assumptions entryListMissingGuard.
Print Assumptions entryListWrongMask.

Lemma entryStringNativeImage `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> 184 <= bv_unsigned prefix <= 191 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 73) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  ⊢ (⌜decodeItemRejectedFacts args /\
    decodeItemBeforeStorage args = decodeItemBeforeStorage args⌝ : iProp Sigma)%I.
Proof. intros. iPureIntro. split; [entry_guard_registered | reflexivity]. Qed.
Print Assumptions entryStringNativeImage.

Lemma entryListNativeImage `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (register : bv 64) (prefix : byte) (rest : list byte) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> 248 <= bv_unsigned prefix <= 255 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_signed (bv_zero_extend 128 (bv_and (register + 9) 255)) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) ->
  ⊢ (⌜decodeItemRejectedFacts args /\
    decodeItemBeforeStorage args = decodeItemBeforeStorage args⌝ : iProp Sigma)%I.
Proof. intros. iPureIntro. split; [entry_guard_registered | reflexivity]. Qed.
Print Assumptions entryListNativeImage.
