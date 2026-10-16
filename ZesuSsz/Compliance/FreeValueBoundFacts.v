Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Compliance.FreeClassFacts.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Lemma freeWellFormedLengthWordBounds args :
  freeArgsWellFormed args -> 0 <= freeBufferLength args < 2 ^ 64.
Proof.
  intros (Hlength & _). exact Hlength.
Qed.

Lemma freeWellFormedAlignmentWordBounds args :
  freeArgsWellFormed args -> 0 <= freeLog2Alignment args < 2 ^ 64.
Proof.
  intros (_ & Halignment & _).
  change (0 <= freeLog2Alignment args < 18446744073709551616).
  lia.
Qed.

Lemma freeSizeClassWordBounds size :
  0 <= freeSizeClassOfBytes size < 2 ^ 64.
Proof.
  pose proof (freeSizeClassOfBytesRange size) as Hrange.
  change (0 <= freeSizeClassOfBytes size < 18446744073709551616).
  lia.
Qed.
