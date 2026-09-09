From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerBasic.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerCore.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerFull.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerActual.

Import ListNotations.

Theorem writeSuccessConcreteRepresentationInhabitedScratchCounterexample :
  exists decoded memory owner scratch copied,
    writeSuccessConcreteRepresentation decoded memory owner /\
    writeSuccessMemorySlice memory owner 32 [0] /\
    scratch = writeSuccessBlockerScratch /\
    copied = writeSuccessBlockerCurrent /\
    ~ writeSuccessConcreteRepresentation decoded
        (write_mem_list memory (Z_to_bv 64 scratch) copied) owner.
Proof.
  exists writeSuccessBlockerDecoded, writeSuccessBlockerRepresentedMemory,
    writeSuccessBlockerOwner, writeSuccessBlockerScratch,
    writeSuccessBlockerCurrent.
  destruct writeSuccessConcreteRepresentationActualScratchCounterexample as
    (Hbefore & Hafter).
  split; [exact Hbefore|].
  split; [exact writeSuccessBlockerExtraData|].
  split; [reflexivity|].
  split; [reflexivity|].
  exact Hafter.
Qed.

Print Assumptions writeSuccessBlockerFullRepresentation.
Print Assumptions writeSuccessConcreteRepresentationActualScratchCounterexample.
Print Assumptions
  writeSuccessConcreteRepresentationInhabitedScratchCounterexample.
