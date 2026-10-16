Require Import ZesuSsz.Automation.All.
Require Import lithium.simpl_classes.
Require Import ZesuSsz.Compliance.FreeValueBoundFacts.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Compliance.FreeClassFacts.
Open Scope Z_scope.

(* These data hints use the existing SimplAnd consumer. *)

#[export] Hint Extern 1 (SimplAnd (0 <= freeBufferLength ?args < 2 ^ 64) True) =>
  match goal with Hwell : freeArgsWellFormed args |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (freeWellFormedLengthWordBounds args Hwell) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (0 <= freeBufferLength ?args) True) =>
  match goal with Hwell : freeArgsWellFormed args |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (proj1 (freeWellFormedLengthWordBounds args Hwell)) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (freeBufferLength ?args < 2 ^ 64) True) =>
  match goal with Hwell : freeArgsWellFormed args |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (proj2 (freeWellFormedLengthWordBounds args Hwell)) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (0 <= freeLog2Alignment ?args < 2 ^ 64) True) =>
  match goal with Hwell : freeArgsWellFormed args |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (freeWellFormedAlignmentWordBounds args Hwell) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (0 <= freeLog2Alignment ?args) True) =>
  match goal with Hwell : freeArgsWellFormed args |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (proj1 (freeWellFormedAlignmentWordBounds args Hwell)) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (freeLog2Alignment ?args < 2 ^ 64) True) =>
  match goal with Hwell : freeArgsWellFormed args |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (proj2 (freeWellFormedAlignmentWordBounds args Hwell)) | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (0 <= freeSizeClassOfBytes ?size <= 22) True) =>
  unfold SimplAnd; split;
  [intros _; exact (freeSizeClassOfBytesRange size) | intros _; exact I] : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (0 <= freeSizeClassOfBytes ?size) True) =>
  unfold SimplAnd; split;
  [intros _; exact (proj1 (freeSizeClassOfBytesRange size)) | intros _; exact I] : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (freeSizeClassOfBytes ?size <= 22) True) =>
  unfold SimplAnd; split;
  [intros _; exact (proj2 (freeSizeClassOfBytesRange size)) | intros _; exact I] : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (0 <= freeSizeClassOfBytes ?size < 2 ^ 64) True) =>
  unfold SimplAnd; split;
  [intros _; exact (freeSizeClassWordBounds size) | intros _; exact I] : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (freeSizeClassOfBytes ?size < 2 ^ 64) True) =>
  unfold SimplAnd; split;
  [intros _; exact (proj2 (freeSizeClassWordBounds size)) | intros _; exact I] : typeclass_instances.
