From Coq Require Import Lists.List.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerCore.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerFull.

Import ListNotations.

Theorem writeSuccessConcreteRepresentationActualScratchCounterexample :
  writeSuccessConcreteRepresentation writeSuccessBlockerDecoded
    writeSuccessBlockerRepresentedMemory writeSuccessBlockerOwner /\
  ~ writeSuccessConcreteRepresentation writeSuccessBlockerDecoded
      (writeSuccessBlockerAfter writeSuccessBlockerRepresentedMemory)
      writeSuccessBlockerOwner.
Proof.
  eapply writeSuccessConcreteRepresentationScratchCounterexample.
  - exact writeSuccessBlockerFullRepresentation.
  - reflexivity.
  - native_compute; reflexivity.
Qed.
