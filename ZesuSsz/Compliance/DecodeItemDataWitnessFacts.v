Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith List Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Lemma decodeItemOutputFlagOffset (args : DecodeItemArgs) :
  Z.of_nat 32 = decodeItemOutputPointer args + 32 - decodeItemOutputPointer args.
Proof. lia. Qed.

#[export] Instance decodeItemOutputFlagOffsetHint (args : DecodeItemArgs) :
  SimplAnd (Z.of_nat 32 =
    decodeItemOutputPointer args + 32 - decodeItemOutputPointer args) True.
Proof. unfold SimplAnd. split; [intros _; apply decodeItemOutputFlagOffset | intros _; exact I]. Qed.

Lemma decodeItemOutputFlagWriteBound (storage : list byte) (width : N) :
  length storage = 40%nat -> (width <= 8)%N ->
  (32 + N.to_nat width <= length storage)%nat.
Proof. intros Hlength Hwidth. rewrite Hlength. lia. Qed.

#[export] Hint Extern 1
  (SimplAnd ((32 + N.to_nat ?width <= length ?storage)%nat) True) =>
  assert_fails (has_evar width);
  match goal with Hlength : length storage = 40%nat |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemOutputFlagWriteBound storage width Hlength); lia
    | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemOutputFlagOffset.
Print Assumptions decodeItemOutputFlagOffsetHint.
Print Assumptions decodeItemOutputFlagWriteBound.

Lemma decodeItemLongStringHeaderWidth (prefix : byte) :
  184 <= bv_unsigned prefix <= 191 -> 1 <= bv_unsigned prefix - 183 <= 8.
Proof. lia. Qed.

Lemma decodeItemLongListHeaderWidth (prefix : byte) :
  248 <= bv_unsigned prefix <= 255 -> 1 <= bv_unsigned prefix - 247 <= 8.
Proof. lia. Qed.

#[export] Hint Extern 1
  (SimplAnd (1 <= bv_unsigned ?prefix - 183 <= 8) True) =>
  match goal with Hclass : 184 <= bv_unsigned prefix <= 191 |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLongStringHeaderWidth prefix Hclass) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (1 <= bv_unsigned ?prefix - 247 <= 8) True) =>
  match goal with Hclass : 248 <= bv_unsigned prefix <= 255 |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemLongListHeaderWidth prefix Hclass) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemLongStringHeaderWidth.
Print Assumptions decodeItemLongListHeaderWidth.
