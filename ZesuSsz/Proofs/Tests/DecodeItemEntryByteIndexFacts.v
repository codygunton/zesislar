Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Ltac entry_index_registration :=
  lazymatch goal with |- @ZesuPureFactIntro ?Sigma ?target _ =>
    let evidence := constr:(_ : @ZesuPureFactIntro Sigma target _) in exact evidence
  end.

Lemma entryByteLiteralScope `{!islaG Sigma} args (prefix : byte) rest
    (continuation : nat -> iProp Sigma) :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) ->
  decodeItemInputHead args prefix rest ->
  @ZesuPureFactIntro Sigma
    (∃ index : nat, ⌜Z.of_nat index =
      (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I
    (⌜decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
      decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8)⌝ ∗
     ⌜decodeItemInputHead args prefix rest⌝ ∗ continuation 0%nat)%I.
Proof. intros Hrange Hhead. entry_index_registration. Qed.

Lemma entryByteUnreducedScope `{!islaG Sigma} args (prefix : byte) rest
    (continuation : nat -> iProp Sigma) :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) ->
  decodeItemInputHead args prefix rest ->
  @ZesuPureFactIntro Sigma
    (∃ index : nat, ⌜Z.of_nat index =
      (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` Z.of_N 1⌝ ∗ continuation index)%I
    (⌜decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
      decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8)⌝ ∗
     ⌜decodeItemInputHead args prefix rest⌝ ∗ continuation 0%nat)%I.
Proof. intros Hrange Hhead. entry_index_registration. Qed.

Lemma entryByteBoundScope args :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) ->
  (0 < length (decodeItemInputBytes args))%nat.
Proof.
  intros Hrange. let fact := constr:(_ : SimplAnd ((0 < length (decodeItemInputBytes args))%nat) True) in
  exact (proj1 fact I).
Qed.

Lemma entryByteLookupScope args (prefix : byte) rest :
  decodeItemInputHead args prefix rest -> decodeItemInputBytes args !! 0%nat = Some prefix.
Proof.
  intros Hhead. let fact := constr:(_ : SimplAnd (decodeItemInputBytes args !! 0%nat = Some prefix) True) in
  exact (proj1 fact I).
Qed.

Lemma entryByteLoadContinuationScope `{!islaG Sigma} args (prefix : byte) rest
    (loadContinuation : nat -> byte -> iProp Sigma) :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) ->
  decodeItemInputHead args prefix rest ->
  ⊢ ((∀ loaded : byte, ⌜decodeItemInputBytes args !! 0%nat = Some loaded⌝ -∗
        loadContinuation 0%nat loaded) -∗
      ∃ index : nat,
        ⌜Z.of_nat index = (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 1⌝ ∗
        ⌜(index < length (decodeItemInputBytes args))%nat⌝ ∗
        ∀ loaded : byte, ⌜decodeItemInputBytes args !! index = Some loaded⌝ -∗
          loadContinuation index loaded)%I.
Proof.
  intros Hrange Hhead. iIntros "Hload".
  pose (K := fun index : nat =>
    (⌜(index < length (decodeItemInputBytes args))%nat⌝ ∗
     ∀ loaded : byte, ⌜decodeItemInputBytes args !! index = Some loaded⌝ -∗
       loadContinuation index loaded)%I).
  pose proof (ltac:(entry_index_registration) : @ZesuPureFactIntro Sigma
    (∃ index : nat, ⌜Z.of_nat index =
      (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 1⌝ ∗ K index)%I _) as Hintro.
  unfold ZesuPureFactIntro in Hintro. iApply Hintro.
  iSplit; [done |]. iSplit; [done |]. unfold K. iFrame.
  iPureIntro. exact (decodeItemEntryByteBound args Hrange).
Qed.

Ltac reject_entry_index target :=
  tryif let evidence := constr:(_ : ZesuPureFactIntro target _) in idtac
  then fail "unexpected entry-byte registration" else exact I.

Lemma entryByteMissingRangeReject `{!islaG Sigma} args (prefix : byte) rest
    (continuation : nat -> iProp Sigma) : decodeItemInputHead args prefix rest -> True.
Proof.
  intros Hhead. reject_entry_index ((∃ index : nat, ⌜Z.of_nat index =
    (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I).
Qed.

Lemma entryByteMissingHeadReject `{!islaG Sigma} args
    (continuation : nat -> iProp Sigma) :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) -> True.
Proof.
  intros Hrange. reject_entry_index ((∃ index : nat, ⌜Z.of_nat index =
    (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I).
Qed.

Lemma entryByteWrongDivisorReject `{!islaG Sigma} args (prefix : byte) rest
    (continuation : nat -> iProp Sigma) :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) ->
  decodeItemInputHead args prefix rest -> True.
Proof.
  intros Hrange Hhead. reject_entry_index ((∃ index : nat, ⌜Z.of_nat index =
    (decodeItemInputPointer args + 0 - decodeItemInputPointer args) `div` 2⌝ ∗ continuation index)%I).
Qed.

Lemma entryByteWrongAddressReject `{!islaG Sigma} args (prefix : byte) rest
    (continuation : nat -> iProp Sigma) :
  decodeItemInputPointer args <= decodeItemInputPointer args + 0 <
    decodeItemInputPointer args + length (decodeItemInputBytes args) * Z.of_N (8 `div` 8) ->
  decodeItemInputHead args prefix rest -> True.
Proof.
  intros Hrange Hhead. reject_entry_index ((∃ index : nat, ⌜Z.of_nat index =
    (decodeItemInputPointer args + 1 - decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I).
Qed.

Print Assumptions entryByteLiteralScope.
Print Assumptions entryByteUnreducedScope.
Print Assumptions entryByteBoundScope.
Print Assumptions entryByteLookupScope.
Print Assumptions entryByteLoadContinuationScope.
Print Assumptions entryByteMissingRangeReject.
Print Assumptions entryByteMissingHeadReject.
Print Assumptions entryByteWrongDivisorReject.
Print Assumptions entryByteWrongAddressReject.
