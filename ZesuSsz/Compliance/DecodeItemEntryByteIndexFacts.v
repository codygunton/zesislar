Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemEntryByteIndex args :
  Z.of_nat 0 =
    (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 1.
Proof. rewrite Z.div_1_r. lia. Qed.

Lemma decodeItemEntryByteBound args :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) ->
  (0 < length (decodeItemInputBytes args))%nat.
Proof. cbn. lia. Qed.

Lemma decodeItemEntryByteLookup args prefix rest :
  decodeItemInputHead args prefix rest ->
  decodeItemInputBytes args !! 0%nat = Some prefix.
Proof.
  intros Hhead. unfold decodeItemInputHead in Hhead. rewrite Hhead. reflexivity.
Qed.

Lemma decodeItemEntryByteIndexWitness `{!islaG Sigma}
    args (prefix : byte) rest (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (∃ index : nat,
      ⌜Z.of_nat index =
        (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 1⌝ ∗
      continuation index)%I
    (⌜decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
      decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8)⌝ ∗
     ⌜decodeItemInputHead args prefix rest⌝ ∗ continuation 0%nat)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "(%Hrange & %Hhead & Hcontinuation)".
  iExists 0%nat. iFrame. iPureIntro. apply decodeItemEntryByteIndex.
Qed.

#[export] Hint Extern 1
  (@ZesuPureFactIntro ?Sigma ?target _) =>
  lazymatch target with
  | (∃ index : nat,
      ⌜Z.of_nat index =
        (decodeItemInputPointer ?args + 0 - decodeItemInputPointer ?args) `div` ?divisor⌝ ∗
      ?continuation index)%I =>
  lazymatch divisor with 1 => idtac | Z.of_N 1 => idtac end;
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
    let Hrange := constr:(ltac:(eassumption) :
      decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
      decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8)) in
    exact (@decodeItemEntryByteIndexWitness Sigma _ args prefix rest continuation)
  end
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd ((0 < length (decodeItemInputBytes ?args))%nat) True) =>
  let Hrange := constr:(ltac:(eassumption) :
    decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8)) in
  unfold SimplAnd; split;
  [intros _; exact (decodeItemEntryByteBound args Hrange) | intros _; exact I]
  : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemInputBytes ?args !! 0%nat = Some ?prefix) True) =>
  match goal with Hhead : decodeItemInputHead args prefix ?rest |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemEntryByteLookup args prefix rest Hhead) | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemEntryByteIndex.
Print Assumptions decodeItemEntryByteBound.
Print Assumptions decodeItemEntryByteLookup.
Print Assumptions decodeItemEntryByteIndexWitness.
