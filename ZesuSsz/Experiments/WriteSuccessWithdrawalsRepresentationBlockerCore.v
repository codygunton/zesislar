From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessParserLemmas.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerBasic.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerInline.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerLists.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerTail.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessBlockerSlicePermitted memory :
  writeSuccessMemoryInteger memory
    (writeSuccessBlockerOwner + 32) 8 writeSuccessBlockerScratch ->
  writeSuccessMemoryInteger memory
    (writeSuccessBlockerOwner + 40) 8 1 ->
  writeSuccessMemoryBytes memory writeSuccessBlockerScratch [0] ->
  writeSuccessMemorySlice memory writeSuccessBlockerOwner 32 [0].
Proof.
  intros Hpointer Hlength Hbyte.
  exists writeSuccessBlockerScratch. split.
  - change (0 <= 536876752 < 18446744073709551616)%Z. lia.
  - repeat split; assumption.
Qed.

Definition writeSuccessBlockerAfter (memory : mem_map) : mem_map :=
  write_mem_list memory (Z_to_bv 64 writeSuccessBlockerScratch)
    writeSuccessBlockerCurrent.

Lemma writeSuccessBlockerOverwrite memory :
  read_mem_list (writeSuccessBlockerAfter memory)
    writeSuccessBlockerScratch 1%N = Some [Z_to_bv 8 1].
Proof.
  have Hrange : islaMemoryRange writeSuccessBlockerScratch 48.
  { unfold islaMemoryRange, writeSuccessBlockerScratch. cbn. lia. }
  have Hread := read_mem_list_written memory writeSuccessBlockerScratch
    writeSuccessBlockerCurrent Hrange.
  rewrite writeSuccessBlockerCurrentLength in Hread.
  pose proof (read_mem_list_split _ _ 1 47 _ Hread) as
    (first & rest & Hparts & HfirstLength & HrestLength & Hfirst & Hrest).
  unfold writeSuccessBlockerCurrent in Hparts.
  destruct first as [|byte first]; cbn in HfirstLength; first discriminate.
  destruct first; cbn in HfirstLength; last discriminate.
  cbn in Hparts. inversion Hparts. subst byte.
  exact Hfirst.
Qed.

Lemma writeSuccessBlockerHeaderPreserved memory :
  writeSuccessMemoryInteger memory
    (writeSuccessBlockerOwner + 32) 8 writeSuccessBlockerScratch ->
  writeSuccessMemoryInteger (writeSuccessBlockerAfter memory)
    (writeSuccessBlockerOwner + 32) 8 writeSuccessBlockerScratch.
Proof.
  intro Hheader.
  unfold writeSuccessMemoryInteger, writeSuccessMemoryBytes in *.
  unfold writeSuccessBlockerAfter.
  eapply read_mem_list_write_mem_list_disjoint; try exact Hheader.
  - unfold islaMemoryRange, writeSuccessBlockerScratch.
    rewrite writeSuccessBlockerCurrentLength. cbn. lia.
  - unfold islaMemoryRangesDisjoint, writeSuccessBlockerScratch,
      writeSuccessBlockerOwner.
    rewrite writeSuccessBlockerCurrentLength.
    rewrite writeSuccessLayoutLeEq. rewrite writeSuccessEncodeLeLength.
    left. cbn. lia.
Qed.

Lemma writeSuccessBlockerSliceFails memory :
  writeSuccessMemoryInteger memory
    (writeSuccessBlockerOwner + 32) 8 writeSuccessBlockerScratch ->
  ~ writeSuccessMemorySlice (writeSuccessBlockerAfter memory)
      writeSuccessBlockerOwner 32 [0].
Proof.
  intros Hheader Hslice.
  destruct Hslice as (pointer & HpointerRange & Hpointer & Hlength & Hbyte).
  have HscratchHeader := writeSuccessBlockerHeaderPreserved memory Hheader.
  have HpointerEq : pointer = writeSuccessBlockerScratch.
  { eapply writeSuccessMemoryInteger64Injective with
      (first := pointer) (second := writeSuccessBlockerScratch).
    - unfold writeSuccessUnsignedValid. cbn. exact HpointerRange.
    - unfold writeSuccessUnsignedValid.
      change (0 <= 536876752 < 18446744073709551616)%Z. lia.
    - exact Hpointer.
    - exact HscratchHeader. }
  subst pointer.
  unfold writeSuccessMemoryBytes in Hbyte.
  cbn in Hbyte.
  pose proof (writeSuccessBlockerOverwrite memory) as Hoverwrite.
  rewrite Hoverwrite in Hbyte. inversion Hbyte.
Qed.

Theorem writeSuccessConcreteRepresentationScratchCounterexample
    decoded memory :
  writeSuccessConcreteRepresentation decoded memory writeSuccessBlockerOwner ->
  observationExtraData decoded = [0] ->
  writeSuccessMemoryInteger memory
    (writeSuccessBlockerOwner + 32) 8 writeSuccessBlockerScratch ->
  writeSuccessConcreteRepresentation decoded memory writeSuccessBlockerOwner /\
  ~ writeSuccessConcreteRepresentation decoded
      (writeSuccessBlockerAfter memory) writeSuccessBlockerOwner.
Proof.
  intros Hrepresentation Hextra Hheader. split; first exact Hrepresentation.
  intro Hafter.
  apply (writeSuccessBlockerSliceFails memory Hheader).
  pose proof (writeSuccessRepresentationExtraData _ _ _ Hafter) as Hslice.
  rewrite Hextra in Hslice. exact Hslice.
Qed.

Print Assumptions writeSuccessBlockerSlicePermitted.
Print Assumptions writeSuccessBlockerOverwrite.
Print Assumptions writeSuccessBlockerHeaderPreserved.
Print Assumptions writeSuccessBlockerSliceFails.
Print Assumptions writeSuccessConcreteRepresentationScratchCounterexample.
