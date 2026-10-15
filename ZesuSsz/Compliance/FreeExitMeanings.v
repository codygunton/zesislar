Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
Require Import ZesuSsz.Contracts.AbiBytes.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma freeReturn42144Meaning `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042144 args x1 x2 x8 x10 x11 x12 x13 x14
    bufferBytes listBytes frameBytes ⊢
  ⌜freeAllows args
    {| freeAfterBuffer := bufferBytes; freeAfterLists := listBytes |}⌝.
Proof.
  unfold freeEntryAt80042144.
  iIntros "(Hcore & %Hbranch)".
  iEval (unfold freeBlockCore) in "Hcore".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro. unfold freeBlockFacts in Hbranch.
  destruct Hbranch as (_ & Hclass).
  destruct Hcore as (_ & _ & _ & _ & _ & Hbuffer & Hlists & _).
  unfold freeAllows, freeResultImages. cbn [freeAfterBuffer freeAfterLists].
  assert (Hguard : (freeSizeClass (freeBufferLength args) (freeLog2Alignment args) <? freeListCount) = false).
  { apply Z.ltb_ge. exact Hclass. }
  rewrite Hguard. exact (conj Hbuffer Hlists).
Qed.

Lemma freeReturn42160Meaning `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042160 args x1 x2 x8 x10 x11 x12 x13 x14
    bufferBytes listBytes frameBytes ⊢
  ⌜forall after : FreeOutcome,
    freeAfterBuffer after = freeReplaceWord bufferBytes 0
      (firstn 8 (skipn (Z.to_nat (8 * freeSizeClass (freeBufferLength args)
        (freeLog2Alignment args))) listBytes)) /\
    freeAfterLists after = freeReplaceWord listBytes
      (Z.to_nat (8 * freeSizeClass (freeBufferLength args) (freeLog2Alignment args)))
      (word64Bytes (freeBufferPointer args)) ->
    freeAllows args after⌝.
Proof.
  unfold freeEntryAt80042160.
  iIntros "(Hcore & %Hbranch)".
  iEval (unfold freeBlockCore) in "Hcore".
  iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro. unfold freeBlockFacts in Hbranch.
  destruct Hbranch as (_ & _ & Hclass).
  destruct Hcore as (_ & _ & _ & _ & _ & Hbuffer & Hlists & _).
  intros after Himages. unfold freeAllows, freeResultImages.
  assert (Hguard : (freeSizeClass (freeBufferLength args) (freeLog2Alignment args) <? freeListCount) = true).
  { apply Z.ltb_lt. exact (proj2 Hclass). }
  rewrite Hguard. rewrite <- Hbuffer. rewrite <- Hlists. exact Himages.
Qed.
