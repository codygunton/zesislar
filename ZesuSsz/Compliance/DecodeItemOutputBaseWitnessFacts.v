Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Compliance.DecodeItemRawOutputFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemOutputBaseOffset (args : DecodeItemArgs) :
  Z.of_nat 0 = decodeItemOutputPointer args + 0 - decodeItemOutputPointer args.
Proof. lia. Qed.

#[export] Instance decodeItemOutputBaseOffsetHint (args : DecodeItemArgs) :
  SimplAnd (Z.of_nat 0 =
    decodeItemOutputPointer args + 0 - decodeItemOutputPointer args) True.
Proof. unfold SimplAnd; split; [intros _; apply decodeItemOutputBaseOffset | intros _; exact I]. Qed.

Lemma decodeItemFlagUpdatedBaseBound (storage : list byte) (first second : byte) (width : N) :
  length storage = 40%nat -> (width <= 8)%N ->
  (0 + N.to_nat width <= length (firstn 32 storage ++ first :: second :: skipn 34 storage))%nat.
Proof.
  intros Hlength Hwidth.
  rewrite app_length firstn_length. cbn [length].
  rewrite skipn_length Hlength. simpl. lia.
Qed.

#[export] Hint Extern 1
  (SimplAnd ((0 + N.to_nat ?width <=
    length (firstn 32 ?storage ++ ?first :: ?second :: skipn 34 ?storage))%nat) True) =>
  assert_fails (has_evar width);
  unfold SimplAnd; split;
  [intros _; apply decodeItemFlagUpdatedBaseBound; [eassumption | lia] | intros _; exact I]
  : typeclass_instances.

Print Assumptions decodeItemOutputBaseOffset.
Print Assumptions decodeItemOutputBaseOffsetHint.
Print Assumptions decodeItemFlagUpdatedBaseBound.

Lemma decodeItemOutputOffset8 (args : DecodeItemArgs) :
  Z.of_nat 8 = decodeItemOutputPointer args + 8 - decodeItemOutputPointer args.
Proof. lia. Qed.

#[export] Instance decodeItemOutputOffset8Hint (args : DecodeItemArgs) :
  SimplAnd (Z.of_nat 8 =
    decodeItemOutputPointer args + 8 - decodeItemOutputPointer args) True.
Proof. unfold SimplAnd; split; [intros _; apply decodeItemOutputOffset8 | intros _; exact I]. Qed.

Print Assumptions decodeItemOutputOffset8.
Print Assumptions decodeItemOutputOffset8Hint.
