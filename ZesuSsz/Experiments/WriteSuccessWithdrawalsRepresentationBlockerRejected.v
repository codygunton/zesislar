From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessStackRange.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerBasic.

Open Scope Z_scope.
Import ListNotations.

Theorem writeSuccessBlockerEntryRejected :
  ~ writeSuccessConcreteRepresentationOff 0x200017d0
      writeSuccessBlockerDecoded writeSuccessBlockerRepresentedMemory
      writeSuccessBlockerOwner.
Proof.
  intro Hrepresentation.
  unfold writeSuccessConcreteRepresentationOff,
    writeSuccessConcreteRepresentationOk,
    writeSuccessConcreteRepresentationHeaderOk in Hrepresentation.
  assert (Hslice : writeSuccessMemorySliceOk
      (writeSuccessAvoidsRange
        (writeSuccessCalleeStackLow 0x200017d0) 0x200017d0)
      writeSuccessBlockerRepresentedMemory writeSuccessBlockerOwner 32
      (observationExtraData writeSuccessBlockerDecoded)).
  { tauto. }
  change (writeSuccessMemorySliceOk
    (writeSuccessAvoidsRange
      (writeSuccessCalleeStackLow 0x200017d0) 0x200017d0)
    writeSuccessBlockerRepresentedMemory writeSuccessBlockerOwner 32 [0])
    in Hslice.
  destruct Hslice as
    (pointer & HpointerRange & HpointerRead & HlengthRead & Hbytes).
  destruct Hbytes as [_ Havoids].
  assert (Hpointer : pointer = writeSuccessBlockerScratch).
  { eapply writeSuccessMemoryInteger64Injective with
      (first := pointer) (second := writeSuccessBlockerScratch).
    - unfold writeSuccessUnsignedValid. cbn. exact HpointerRange.
    - unfold writeSuccessUnsignedValid.
      change (0 <= 536876752 < 18446744073709551616)%Z. lia.
    - exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ HpointerRead).
    - exact writeSuccessBlockerExtraDataHeader. }
  subst pointer.
  unfold writeSuccessAvoidsRange, writeSuccessCalleeStackLow,
    writeSuccessHelperStackDepth, writeSuccessBlockerScratch in Havoids.
  cbn in Havoids. lia.
Qed.

Print Assumptions writeSuccessBlockerEntryRejected.
