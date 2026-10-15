Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation.ReturnRoute.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
Require Import ZesuSsz.Compliance.FreeExitMeanings.
Require Import ZesuSsz.Compliance.FreeReturnFacts.
From Coq Require Import List ZArith.
Open Scope Z_scope.

#[export] Instance freeReturn42144MeaningRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuExitMeaning
    (freeEntryAt80042144 args x1 x2 x8 x10 x11 x12 x13 x14
      bufferBytes listBytes frameBytes)
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes))) =
      Z_to_bv 64 (freeReturnAddress args) /\
     freeAllows args
    {| freeAfterBuffer := bufferBytes; freeAfterLists := listBytes |}).
Proof.
  change ((freeEntryAt80042144 args x1 x2 x8 x10 x11 x12 x13 x14
      bufferBytes listBytes frameBytes) ⊢ ⌜Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes))) =
      Z_to_bv 64 (freeReturnAddress args) /\
     freeAllows args
    {| freeAfterBuffer := bufferBytes; freeAfterLists := listBytes |}⌝).
  rewrite bi.pure_and. apply bi.and_intro.
  { unfold freeEntryAt80042144.
    iIntros "(Hcore & _)". iApply freeBlockCoreReturnDecoder. iExact "Hcore". }
  { apply freeReturn42144Meaning. }
Qed.

#[export] Instance freeReturn42160MeaningRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuExitMeaning
    (freeEntryAt80042160 args x1 x2 x8 x10 x11 x12 x13 x14
      bufferBytes listBytes frameBytes)
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes))) =
      Z_to_bv 64 (freeReturnAddress args) /\
     forall after : FreeOutcome,
    freeAfterBuffer after = freeReplaceWord bufferBytes 0
      (firstn 8 (skipn (Z.to_nat (8 + 8 * freeSizeClass (freeBufferLength args)
        (freeLog2Alignment args))) listBytes)) /\
    freeAfterLists after = freeReplaceWord listBytes
      (Z.to_nat (8 + 8 * freeSizeClass (freeBufferLength args) (freeLog2Alignment args)))
      (word64Bytes (freeBufferPointer args)) ->
    freeAllows args after).
Proof.
  change ((freeEntryAt80042160 args x1 x2 x8 x10 x11 x12 x13 x14
      bufferBytes listBytes frameBytes) ⊢ ⌜Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes))) =
      Z_to_bv 64 (freeReturnAddress args) /\
     forall after : FreeOutcome,
    freeAfterBuffer after = freeReplaceWord bufferBytes 0
      (firstn 8 (skipn (Z.to_nat (8 + 8 * freeSizeClass (freeBufferLength args)
        (freeLog2Alignment args))) listBytes)) /\
    freeAfterLists after = freeReplaceWord listBytes
      (Z.to_nat (8 + 8 * freeSizeClass (freeBufferLength args) (freeLog2Alignment args)))
      (word64Bytes (freeBufferPointer args)) ->
    freeAllows args after⌝).
  rewrite bi.pure_and. apply bi.and_intro.
  { unfold freeEntryAt80042160.
    iIntros "(Hcore & _)". iApply freeBlockCoreReturnDecoder. iExact "Hcore". }
  { apply freeReturn42160Meaning. }
Qed.

