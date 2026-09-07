From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d4.
Require Import IslaTraces.write_success_02.a101d8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep156a4.

Open Scope Z_scope.

Lemma writeSuccess156a4MstatusPreserved regs :
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp (writeSuccess156a4Regs regs) writeSuccess15694Mstatus =
    Some (Val_Bool true).
Proof.
  intros Hmstatus. unfold writeSuccess156a4Regs, writeSuccess15694Mstatus in *.
  cbn in *. rewrite !lookup_insert_ne; try discriminate. exact Hmstatus.
Qed.

Lemma writeSuccessWithdrawalsPhase101d8Zero state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d8 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 0)) ->
  writeSuccessWithdrawalsPhaseRemaining state = 404%nat.
Proof.
  intros Hpc Hx15. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_101d8_zero state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d8 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 0)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 404)%nat.
Proof.
  intros Hpc Hx15 Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101d8Zero state Hpc Hx15.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 404 =
    410 * remaining + 404)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsPhase101e0Zero state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101e0 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 0)) ->
  writeSuccessWithdrawalsPhaseRemaining state = 403%nat.
Proof.
  intros Hpc Hx15. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_101e0_zero state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x101e0 ->
  state.1.1.(seq_regs) !! "x15" = Some (RVal_Bits (BV 64 0)) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 403)%nat.
Proof.
  intros Hpc Hx15 Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101e0Zero state Hpc Hx15.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 403 =
    410 * remaining + 403)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawals101d4Context args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state observations94 state98 observations98
    state9c observations9c statea0 observationsa0 statea4 observationsa4
    state101d4 :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  IslaInstructionSegment state.1 observations94 state98 ->
  IslaInstructionSegment state98 observations98 state9c ->
  IslaInstructionSegment state9c observations9c statea0 ->
  IslaInstructionSegment statea0 observationsa0 statea4 ->
  IslaInstructionSegment statea4 observationsa4 state101d4 ->
  exists oldX15,
    writeSuccess101d4Before state101d4.1.(seq_regs) state101d4.2 = state101d4 /\
    state101d4.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x101d4)) /\
    state101d4.1.(seq_regs) !! "x15" = Some oldX15 /\
    state101d4.2.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 /\
    state101d4.2.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 /\
    eval_a_exp state101d4.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true) /\
    state101d4.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
    (Z.of_nat (S remaining) < 2 ^ 64)%Z.
Proof.
  intros Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0 Hsegmenta4.
  have Hstate98 := proj1 (writeSuccessWithdrawalsEverySegment15694Decreases args
    sp pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    observations94 state98 Hinv Hsegment94).
  have Hstate9c := proj1 (writeSuccessWithdrawalsEverySegment15698Decreases args
    sp pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    observations94 state98 observations98 state9c Hinv Hsegment94 Hsegment98).
  have Hstatea0 := proj1 (writeSuccessWithdrawalsEverySegment1569cDecreases args
    sp pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    observations94 state98 observations98 state9c observations9c statea0 Hinv
    Hsegment94 Hsegment98 Hsegment9c).
  have Hstatea4 := proj1 (writeSuccessWithdrawalsEverySegment156a0Decreases args
    sp pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    observations94 state98 observations98 state9c observations9c statea0
    observationsa0 statea4 Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0).
  have Hstate101d4 := proj1 (writeSuccessWithdrawalsEverySegment156a4Decreases
    args sp pointer base total processed remaining withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog state
    observations94 state98 observations98 state9c observations9c statea0
    observationsa0 statea4 observationsa4 state101d4 Hinv Hsegment94 Hsegment98
    Hsegment9c Hsegmenta0 Hsegmenta4).
  have Hx15 : exists oldX15, state.1.1.(seq_regs) !! "x15" = Some oldX15 by
    (unfold Inv_15694 in Hinv; tauto).
  destruct Hx15 as [oldX15 Hx15].
  have Htable : writeSuccessWithdrawalsInstructionTable state.1.2 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hcode101d4 : state.1.2.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode101d8 : state.1.2.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hassumptions : writeSuccessTraceAssumptions state.1 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hmstatus := writeSuccess15694MstatusFromTraceAssumptions
    state.1.1.(seq_regs) state.1.2 Hassumptions.
  have Hx9 : state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange := Inv_15694_counter_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinv.
  exists oldX15. repeat split.
  - rewrite Hstate101d4. reflexivity.
  - rewrite Hstate101d4. unfold writeSuccess156a4After,
      writeSuccess15694Local, writeSuccess156a4Regs. cbn.
    rewrite lookup_insert. pose proof writeSuccess156a4ValuesExact as Hvalues.
    destruct Hvalues as (_ & _ & _ & Htarget). rewrite Htarget. reflexivity.
  - rewrite Hstate101d4 Hstatea4 Hstatea0 Hstate9c Hstate98.
    unfold writeSuccess156a4After, writeSuccess156a0After,
      writeSuccess1569cAfter, writeSuccess15698After,
      writeSuccess15694After, writeSuccess1569cLocal,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156a4RegsLookupOther; try discriminate.
    rewrite writeSuccess156a0RegsLookupOther; try discriminate.
    rewrite writeSuccess1569cRegsLookupOther; try discriminate.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx15.
  - rewrite Hstate101d4 Hstatea4 Hstatea0 Hstate9c Hstate98. exact Hcode101d4.
  - rewrite Hstate101d4 Hstatea4 Hstatea0 Hstate9c Hstate98. exact Hcode101d8.
  - rewrite Hstate101d4 Hstatea4 Hstatea0 Hstate9c Hstate98.
    unfold writeSuccess156a4After, writeSuccess156a0After,
      writeSuccess1569cAfter, writeSuccess15698After,
      writeSuccess15694After, writeSuccess1569cLocal,
      writeSuccess15694Local. cbn.
    apply writeSuccess156a4MstatusPreserved.
    apply writeSuccess156a0MstatusPreserved.
    apply writeSuccess1569cMstatusPreserved.
    apply writeSuccess15698MstatusPreserved.
    apply writeSuccess15694MstatusPreserved. exact Hmstatus.
  - rewrite Hstate101d4 Hstatea4 Hstatea0 Hstate9c Hstate98.
    unfold writeSuccess156a4After, writeSuccess156a0After,
      writeSuccess1569cAfter, writeSuccess15698After,
      writeSuccess15694After, writeSuccess1569cLocal,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess156a4RegsLookupOther; try discriminate.
    rewrite writeSuccess156a0RegsLookupOther; try discriminate.
    rewrite writeSuccess1569cRegsLookupOther; try discriminate.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx9.
  - exact Hrange.
Qed.

Print Assumptions writeSuccess156a4MstatusPreserved.
Print Assumptions writeSuccessWithdrawalsPhase101d8Zero.
Print Assumptions rank_15694_at_101d8_zero.
Print Assumptions writeSuccessWithdrawalsPhase101e0Zero.
Print Assumptions rank_15694_at_101e0_zero.
Print Assumptions writeSuccessWithdrawals101d4Context.
