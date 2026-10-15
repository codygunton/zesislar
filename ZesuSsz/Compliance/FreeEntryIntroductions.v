Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.FreeClassFacts.

Lemma freeCandidateClassAccepting args :
  freeArgsWellFormed args -> 3 < freeLog2Alignment args ->
  freeCandidateClass args =
    freeSizeClass (freeBufferLength args) (freeLog2Alignment args).
Proof.
  intros (_ & Halign & _) Hguard.
  assert (Hword : 0 <= freeLog2Alignment args - 3 < bv_modulus 64).
  { unfold bv_modulus. cbn. lia. }
  unfold freeCandidateClass, freeAlignmentWord.
  rewrite (Z_to_bv_small 64 _ Hword).
  unfold freeSizeClass.
  assert (Hpositive : Z.max 0 (freeLog2Alignment args - 3) = freeLog2Alignment args - 3)
    by (apply Z.max_r; lia).
  rewrite Hpositive. reflexivity.
Qed.

Lemma freeEntry42134Introduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042134 args x1 x2 x8 x10 x11 x12 x13 x14
    bufferBytes listBytes frameBytes ⊢
  ⌜x13 = Z_to_bv 64 (freeCandidateClass args) /\
    (3 < freeLog2Alignment args ->
      x13 = Z_to_bv 64
        (freeSizeClass (freeBufferLength args) (freeLog2Alignment args)))⌝.
Proof.
  unfold freeEntryAt80042134.
  iIntros "(Hcore & %Hbranch)".
  iEval (unfold freeBlockCore) in "Hcore".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro. unfold freeBlockFacts in Hbranch.
  destruct Hbranch as (_ & _ & _ & Hclass).
  destruct Hcore as (Hwell & _). split; first exact Hclass.
  intros Hguard. rewrite Hclass.
  rewrite (freeCandidateClassAccepting args Hwell Hguard).
  reflexivity.
Qed.

Lemma freeEntry42154Introduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042154 args x1 x2 x8 x10 x11 x12 x13 x14
    bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64
      (freeSizeClass (freeBufferLength args) (freeLog2Alignment args)) /\
    0 <= freeSizeClass (freeBufferLength args) (freeLog2Alignment args) < 23⌝.
Proof.
  unfold freeEntryAt80042154.
  iIntros "(Hcore & %Hbranch)".
  iPureIntro. unfold freeBlockFacts in Hbranch.
  destruct Hbranch as (_ & Halign & Hclass).
  rewrite (freeSmallAlignmentClass _ _ Halign).
  split; first exact Hclass.
  pose proof (freeSizeClassOfBytesRange (freeBufferLength args)). lia.
Qed.
