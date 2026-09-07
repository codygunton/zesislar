From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d4.
Require Import IslaTraces.write_success_90.a156a4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep.

Open Scope Z_scope.

Lemma writeSuccess156a0MstatusPreserved regs :
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp (writeSuccess156a0Regs regs) writeSuccess15694Mstatus =
    Some (Val_Bool true).
Proof.
  intros Hmstatus. unfold writeSuccess156a0Regs, writeSuccess15694Mstatus in *.
  cbn in *. rewrite !lookup_insert_ne; try discriminate. exact Hmstatus.
Qed.

Lemma writeSuccessWithdrawalsPhase101d4 state :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d4 ->
  writeSuccessWithdrawalsPhaseRemaining state = 405%nat.
Proof.
  intros Hpc. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_101d4 state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d4 ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 405)%nat.
Proof.
  intros Hpc Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101d4 state Hpc.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 405 =
    410 * remaining + 405)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawals156a4Context args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state observations94 state98 observations98
    state9c observations9c statea0 observationsa0 statea4 :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  IslaInstructionSegment state.1 observations94 state98 ->
  IslaInstructionSegment state98 observations98 state9c ->
  IslaInstructionSegment state9c observations9c statea0 ->
  IslaInstructionSegment statea0 observationsa0 statea4 ->
  writeSuccess156a4Before statea4.1.(seq_regs) statea4.2 = statea4 /\
  statea4.1.(seq_regs) !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156a4)) /\
  statea4.1.(seq_regs) !! "x1" = Some (RVal_Bits writeSuccess156a4Ra) /\
  statea4.2.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 /\
  statea4.2.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 /\
  eval_a_exp statea4.1.(seq_regs) writeSuccess15694Mstatus =
    Some (Val_Bool true) /\
  statea4.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) /\
  (Z.of_nat (S remaining) < 2 ^ 64)%Z.
Proof.
  intros Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0.
  destruct (writeSuccessWithdrawalsInv15694Entry args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (oldX10 & Hentry & Hpc94 & Hx1 & Hx10 & Hx11 & Hx12 & Hcode94 & Hcode98 & Hassumptions).
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
  have Htable : writeSuccessWithdrawalsInstructionTable state.1.2 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hcodea4 : state.1.2.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode101d4 : state.1.2.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hmstatus := writeSuccess15694MstatusFromTraceAssumptions
    state.1.1.(seq_regs) state.1.2 Hassumptions.
  have Hx9 : state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange := Inv_15694_counter_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinv.
  repeat split.
  - rewrite Hstatea4. reflexivity.
  - rewrite Hstatea4. unfold writeSuccess156a0After,
      writeSuccess15694Local, writeSuccess156a0Regs. cbn.
    rewrite lookup_insert writeSuccess156a0NextPcExact. reflexivity.
  - rewrite Hstatea4. unfold writeSuccess156a0After,
      writeSuccess15694Local, writeSuccess156a0Regs,
      writeSuccess156a4Ra. cbn. rewrite lookup_insert_ne; try discriminate.
    rewrite lookup_insert. reflexivity.
  - rewrite Hstatea4 Hstatea0 Hstate9c Hstate98. exact Hcodea4.
  - rewrite Hstatea4 Hstatea0 Hstate9c Hstate98. exact Hcode101d4.
  - rewrite Hstatea4 Hstatea0 Hstate9c Hstate98.
    unfold writeSuccess156a0After, writeSuccess1569cAfter,
      writeSuccess15698After, writeSuccess15694After,
      writeSuccess1569cLocal, writeSuccess15694Local. cbn.
    apply writeSuccess156a0MstatusPreserved.
    apply writeSuccess1569cMstatusPreserved.
    apply writeSuccess15698MstatusPreserved.
    apply writeSuccess15694MstatusPreserved. exact Hmstatus.
  - rewrite Hstatea4 Hstatea0 Hstate9c Hstate98.
    unfold writeSuccess156a0After, writeSuccess1569cAfter,
      writeSuccess15698After, writeSuccess15694After,
      writeSuccess1569cLocal, writeSuccess15694Local. cbn.
    rewrite writeSuccess156a0RegsLookupOther; try discriminate.
    rewrite writeSuccess1569cRegsLookupOther; try discriminate.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx9.
  - exact Hrange.
Qed.

Lemma writeSuccessWithdrawalsSegment156a4ExistsAndDecreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists observations94 state98 observations98 state9c observations9c statea0
      observationsa0 statea4 observationsa4 after,
    IslaInstructionSegment state.1 observations94 state98 /\
    IslaInstructionSegment state98 observations98 state9c /\
    IslaInstructionSegment state9c observations9c statea0 /\
    IslaInstructionSegment statea0 observationsa0 statea4 /\
    IslaInstructionSegment statea4 observationsa4 after /\
    dom after.1.(seq_regs) = dom statea4.1.(seq_regs) /\
    rank_15694 (after, state.2) < rank_15694 (statea4, state.2).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsSegment156a0ExistsAndDecreases _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as
    (observations94 & state98 & observations98 & state9c & observations9c &
     statea0 & observationsa0 & statea4 & Hsegment94 & Hsegment98 & Hsegment9c &
     Hsegmenta0 & Hdoma0 & Hranka0).
  destruct (writeSuccessWithdrawals156a4Context args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations94
    state98 observations98 state9c observations9c statea0 observationsa0 statea4
    Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0) as
    (Hbefore & Hpca4 & Hx1 & Hcodea4 & Hcode101d4 & Hmstatus & Hx9 & Hrange).
  pose (observationsa4 := writeSuccess156a4Observations
    statea4.1.(seq_regs) statea4.2).
  pose (after := writeSuccess156a4After statea4.1.(seq_regs) statea4.2).
  have Hsegmenta4 : IslaInstructionSegment statea4 observationsa4 after.
  { rewrite <- Hbefore. apply (proj1 (segment_156a4_mstatus _ _ Hpca4 Hx1
      Hcodea4 Hcode101d4 Hmstatus)). }
  exists observations94, state98, observations98, state9c, observations9c,
    statea0, observationsa0, statea4, observationsa4, after.
  repeat split; try assumption.
  - unfold after, writeSuccess156a4After, writeSuccess15694Local. cbn.
    eapply writeSuccess156a4RegsDom; eassumption.
  - have Hpca4State : writeSuccessWithdrawalsConcretePc (statea4, state.2) =
        Some 0x156a4.
    { rewrite <- Hbefore. unfold writeSuccessWithdrawalsConcretePc. cbn.
      rewrite Hpca4. reflexivity. }
    have Hpc101d4 : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x101d4.
    { unfold after, writeSuccessWithdrawalsConcretePc,
        writeSuccess156a4After, writeSuccess15694Local,
        writeSuccess156a4Regs. cbn.
      rewrite lookup_insert. pose proof writeSuccess156a4ValuesExact as Hvalues.
      destruct Hvalues as (_ & _ & _ & Htarget). rewrite Htarget. reflexivity. }
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold after, writeSuccess156a4After, writeSuccess15694Local. cbn.
      rewrite writeSuccess156a4RegsLookupOther; try discriminate. exact Hx9. }
    rewrite (rank_15694_at_156a4 (statea4, state.2) remaining Hpca4State Hx9
      Hrange).
    rewrite (rank_15694_at_101d4 (after, state.2) remaining Hpc101d4 Hx9After
      Hrange). lia.
Qed.

Lemma writeSuccessWithdrawalsEverySegment156a4Decreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations94 state98
    observations98 state9c observations9c statea0 observationsa0 statea4
    observationsa4 after :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  IslaInstructionSegment state.1 observations94 state98 ->
  IslaInstructionSegment state98 observations98 state9c ->
  IslaInstructionSegment state9c observations9c statea0 ->
  IslaInstructionSegment statea0 observationsa0 statea4 ->
  IslaInstructionSegment statea4 observationsa4 after ->
  after = writeSuccess156a4After statea4.1.(seq_regs) statea4.2 /\
  dom after.1.(seq_regs) = dom statea4.1.(seq_regs) /\
  rank_15694 (after, state.2) < rank_15694 (statea4, state.2).
Proof.
  intros Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0 Hsegmenta4.
  destruct (writeSuccessWithdrawals156a4Context args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations94
    state98 observations98 state9c observations9c statea0 observationsa0 statea4
    Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0) as
    (Hbefore & Hpca4 & Hx1 & Hcodea4 & Hcode101d4 & Hmstatus & Hx9 & Hrange).
  have Hsegmenta4Canonical : IslaInstructionSegment
      (writeSuccess156a4Before statea4.1.(seq_regs) statea4.2)
      observationsa4 after.
  { rewrite Hbefore. exact Hsegmenta4. }
  have Hafter :
      after = writeSuccess156a4After statea4.1.(seq_regs) statea4.2.
  { exact (proj1 (segment_156a4_mstatus_covered _ _ _ _ Hpca4 Hx1
      Hcodea4 Hcode101d4 Hmstatus Hsegmenta4Canonical)). }
  split; first exact Hafter. split.
  - rewrite Hafter. unfold writeSuccess156a4After, writeSuccess15694Local. cbn.
    eapply writeSuccess156a4RegsDom; eassumption.
  - have Hpca4State : writeSuccessWithdrawalsConcretePc (statea4, state.2) =
        Some 0x156a4.
    { rewrite <- Hbefore. unfold writeSuccessWithdrawalsConcretePc. cbn.
      rewrite Hpca4. reflexivity. }
    have Hpc101d4 : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x101d4.
    { rewrite Hafter. unfold writeSuccessWithdrawalsConcretePc,
        writeSuccess156a4After, writeSuccess15694Local,
        writeSuccess156a4Regs. cbn.
      rewrite lookup_insert. pose proof writeSuccess156a4ValuesExact as Hvalues.
      destruct Hvalues as (_ & _ & _ & Htarget). rewrite Htarget. reflexivity. }
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { rewrite Hafter. unfold writeSuccess156a4After,
        writeSuccess15694Local. cbn.
      rewrite writeSuccess156a4RegsLookupOther; try discriminate. exact Hx9. }
    rewrite (rank_15694_at_156a4 (statea4, state.2) remaining Hpca4State Hx9
      Hrange).
    rewrite (rank_15694_at_101d4 (after, state.2) remaining Hpc101d4 Hx9After
      Hrange). lia.
Qed.

Print Assumptions writeSuccess156a0MstatusPreserved.
Print Assumptions writeSuccessWithdrawalsPhase101d4.
Print Assumptions rank_15694_at_101d4.
Print Assumptions writeSuccessWithdrawals156a4Context.
Print Assumptions writeSuccessWithdrawalsSegment156a4ExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment156a4Decreases.
