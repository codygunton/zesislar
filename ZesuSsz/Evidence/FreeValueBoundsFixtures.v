Require Import ZesuSsz.Automation.All.
Require Import lithium.simpl_classes.
Require Import ZesuSsz.Compliance.FreeHints.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Open Scope Z_scope.

Lemma freeBoundHintLengthPair (args : FreeArgs) (Hwell : freeArgsWellFormed args) : 0 <= freeBufferLength args < 2 ^ 64.
Proof.
  let evidence := zesu_registered_pure_fact constr:(0 <= freeBufferLength args < 2 ^ 64) in
  exact evidence.
Qed.

Lemma freeBoundHintLengthLower (args : FreeArgs) (Hwell : freeArgsWellFormed args) : 0 <= freeBufferLength args.
Proof.
  let evidence := zesu_registered_pure_fact constr:(0 <= freeBufferLength args) in
  exact evidence.
Qed.

Lemma freeBoundHintLengthUpper (args : FreeArgs) (Hwell : freeArgsWellFormed args) : freeBufferLength args < 2 ^ 64.
Proof.
  let evidence := zesu_registered_pure_fact constr:(freeBufferLength args < 2 ^ 64) in
  exact evidence.
Qed.

Lemma freeBoundHintAlignmentPair (args : FreeArgs) (Hwell : freeArgsWellFormed args) : 0 <= freeLog2Alignment args < 2 ^ 64.
Proof.
  let evidence := zesu_registered_pure_fact constr:(0 <= freeLog2Alignment args < 2 ^ 64) in
  exact evidence.
Qed.

Lemma freeBoundHintAlignmentLower (args : FreeArgs) (Hwell : freeArgsWellFormed args) : 0 <= freeLog2Alignment args.
Proof.
  let evidence := zesu_registered_pure_fact constr:(0 <= freeLog2Alignment args) in
  exact evidence.
Qed.

Lemma freeBoundHintAlignmentUpper (args : FreeArgs) (Hwell : freeArgsWellFormed args) : freeLog2Alignment args < 2 ^ 64.
Proof.
  let evidence := zesu_registered_pure_fact constr:(freeLog2Alignment args < 2 ^ 64) in
  exact evidence.
Qed.

Lemma freeBoundHintClassRange (size : Z) : 0 <= freeSizeClassOfBytes size <= 22.
Proof.
  let evidence := zesu_registered_pure_fact constr:(0 <= freeSizeClassOfBytes size <= 22) in
  exact evidence.
Qed.

Lemma freeBoundHintClassLower (size : Z) : 0 <= freeSizeClassOfBytes size.
Proof.
  let evidence := zesu_registered_pure_fact constr:(0 <= freeSizeClassOfBytes size) in
  exact evidence.
Qed.

Lemma freeBoundHintClassUpper (size : Z) : freeSizeClassOfBytes size <= 22.
Proof.
  let evidence := zesu_registered_pure_fact constr:(freeSizeClassOfBytes size <= 22) in
  exact evidence.
Qed.

Lemma freeBoundHintClassWordPair (size : Z) : 0 <= freeSizeClassOfBytes size < 2 ^ 64.
Proof.
  let evidence := zesu_registered_pure_fact constr:(0 <= freeSizeClassOfBytes size < 2 ^ 64) in
  exact evidence.
Qed.

Lemma freeBoundHintClassWordUpper (size : Z) : freeSizeClassOfBytes size < 2 ^ 64.
Proof.
  let evidence := zesu_registered_pure_fact constr:(freeSizeClassOfBytes size < 2 ^ 64) in
  exact evidence.
Qed.

Lemma freeBoundHintsRequireWellFormed (args : FreeArgs) : True.
Proof.
  Fail Check (ltac:(typeclasses eauto) : SimplAnd (0 <= freeBufferLength args < 2 ^ 64) True).
  Fail Check (ltac:(typeclasses eauto) : SimplAnd (0 <= freeBufferLength args) True).
  Fail Check (ltac:(typeclasses eauto) : SimplAnd (freeBufferLength args < 2 ^ 64) True).
  Fail Check (ltac:(typeclasses eauto) : SimplAnd (0 <= freeLog2Alignment args < 2 ^ 64) True).
  Fail Check (ltac:(typeclasses eauto) : SimplAnd (0 <= freeLog2Alignment args) True).
  Fail Check (ltac:(typeclasses eauto) : SimplAnd (freeLog2Alignment args < 2 ^ 64) True).
  exact I.
Qed.
