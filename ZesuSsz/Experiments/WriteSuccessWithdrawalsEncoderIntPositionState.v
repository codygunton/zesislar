From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionStateBuild.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRecordedEdgeEndpoint.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedPositions.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsEncoderIntegerSelected state pc (returnAddress : bv 64) :
  In pc [0x15d10; 0x15d14; 0x15d18; 0x15d1c; 0x15d20; 0x15d24;
    0x15d30; 0x15d34] ->
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits returnAddress) ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (writeSuccessWithdrawalsIntegerOccurrence (bv_unsigned returnAddress)).
Proof.
  intros Hpc Hx1.
  unfold writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned.
  cbn in Hpc. decompose [or] Hpc; try contradiction; subst pc; cbn; rewrite Hx1; reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderIntegerSavedSelected state pc (returnAddress : bv 64) :
  (pc = 0x15d28 \/ pc = 0x15d2c) ->
  writeSuccessWithdrawalsSavedReturn state = Some (bv_unsigned returnAddress) ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (writeSuccessWithdrawalsIntegerOccurrence (bv_unsigned returnAddress)).
Proof.
  intros Hpc Hsaved; destruct Hpc as [Hpc|Hpc]; subst pc; unfold writeSuccessWithdrawalsSelectedOccurrence;
    rewrite Hsaved; reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderOutputSelected state pc (returnAddress : bv 64) :
  In pc [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0] ->
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits writeSuccess15d28Link) ->
  writeSuccessWithdrawalsSavedReturn state = Some (bv_unsigned returnAddress) ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (writeSuccessWithdrawalsOutputOccurrence (bv_unsigned returnAddress)).
Proof.
  intros Hpc Hx1 Hsaved.
  unfold writeSuccessWithdrawalsSelectedOccurrence,
    writeSuccessWithdrawalsRegisterUnsigned.
  cbn in Hpc. decompose [or] Hpc; try contradiction; subst pc;
    rewrite Hx1; cbn; rewrite Hsaved; reflexivity.
Qed.

Definition writeSuccessWithdrawalsEncoderIntPositionStart
    (start : nat) (returnAddress : bv 64) : Prop :=
  (start = 347%nat /\ returnAddress = Z_to_bv 64 0x156b4) \/
  (start = 365%nat /\ returnAddress = Z_to_bv 64 0x156c0) \/
  (start = 392%nat /\ returnAddress = Z_to_bv 64 0x156dc).

Definition writeSuccessWithdrawalsEncoderIntExpectedOccurrence
    (returnAddress : bv 64) (offset : nat) : nat :=
  if (offset <? 7)%nat then
    writeSuccessWithdrawalsIntegerOccurrence (bv_unsigned returnAddress)
  else if (offset <? 12)%nat then
    writeSuccessWithdrawalsOutputOccurrence (bv_unsigned returnAddress)
  else writeSuccessWithdrawalsIntegerOccurrence (bv_unsigned returnAddress).

Lemma writeSuccessWithdrawalsEncoderIntPositionTable start returnAddress offset
    pc :
  writeSuccessWithdrawalsEncoderIntPositionStart start returnAddress ->
  (offset < 15)%nat ->
  nth_error writeSuccessWithdrawalsIntegerPcs offset = Some pc ->
  nth_error writeSuccessWithdrawalsIterationPcs (start + offset) = Some pc /\
  writeSuccessWithdrawalsEncoderIntExpectedOccurrence returnAddress offset =
    count_occ Z.eq_dec
      (firstn (start + offset) writeSuccessWithdrawalsIterationPcs) pc.
Proof.
  intros Hstart Hoffset Hpc.
  destruct Hstart as [(-> & ->)|[(-> & ->)|(-> & ->)]].
  all: destruct offset as
    [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|offset]]]]]]]]]]]]]]];
    cbn in Hpc; try lia; injection Hpc as <-; native_compute; split; reflexivity.
Qed.

Theorem writeSuccessWithdrawalsEncoderIntActualPositionState remaining start
    returnAddress offset state pc :
  writeSuccessWithdrawalsEncoderIntPositionStart start returnAddress ->
  (offset < 15)%nat ->
  nth_error writeSuccessWithdrawalsIntegerPcs offset = Some pc ->
  writeSuccessWithdrawalsConcretePc state = Some pc ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (writeSuccessWithdrawalsEncoderIntExpectedOccurrence returnAddress
      offset) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining (start + offset) state.
Proof.
  intros Hstart Hoffset HlocalPc Hpc Hselected Hx9 Hrange.
  destruct (writeSuccessWithdrawalsEncoderIntPositionTable start returnAddress
    offset pc Hstart Hoffset HlocalPc) as (HtablePc & Hoccurrence).
  eapply writeSuccessWithdrawalsPositionStateBuild.
  - destruct Hstart as [(-> & _)|[(-> & _)|(-> & _)]]; lia.
  - exact HtablePc.
  - exact Hpc.
  - rewrite <- Hoccurrence. exact Hselected.
  - exact Hx9.
  - exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntegerSelected.
Print Assumptions writeSuccessWithdrawalsEncoderIntegerSavedSelected.
Print Assumptions writeSuccessWithdrawalsEncoderOutputSelected.
Print Assumptions writeSuccessWithdrawalsEncoderIntPositionTable.
Print Assumptions writeSuccessWithdrawalsEncoderIntActualPositionState.
