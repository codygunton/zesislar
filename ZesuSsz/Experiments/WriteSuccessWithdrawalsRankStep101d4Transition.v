From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep156a4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankStep101d4.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsSegment101d4ExistsAndDecreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists observations94 state98 observations98 state9c observations9c statea0
      observationsa0 statea4 observationsa4 state101d4 observations101d4 after,
    IslaInstructionSegment state.1 observations94 state98 /\
    IslaInstructionSegment state98 observations98 state9c /\
    IslaInstructionSegment state9c observations9c statea0 /\
    IslaInstructionSegment statea0 observationsa0 statea4 /\
    IslaInstructionSegment statea4 observationsa4 state101d4 /\
    IslaInstructionSegment state101d4 observations101d4 after /\
    dom after.1.(seq_regs) = dom state101d4.1.(seq_regs) /\
    rank_15694 (after, state.2) < rank_15694 (state101d4, state.2).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsSegment156a4ExistsAndDecreases _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as
    (observations94 & state98 & observations98 & state9c & observations9c &
     statea0 & observationsa0 & statea4 & observationsa4 & state101d4 &
     Hsegment94 & Hsegment98 & Hsegment9c & Hsegmenta0 & Hsegmenta4 &
     Hdoma4 & Hranka4).
  destruct (writeSuccessWithdrawals101d4Context args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations94
    state98 observations98 state9c observations9c statea0 observationsa0 statea4
    observationsa4 state101d4 Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0
    Hsegmenta4) as
    (oldX15 & Hbefore & Hpc & Hx15 & Hcode & Hnext & Hmstatus & Hx9 & Hrange).
  pose (observations101d4 := writeSuccess101d4Observations
    state101d4.1.(seq_regs) state101d4.2).
  pose (after := writeSuccess101d4After
    state101d4.1.(seq_regs) state101d4.2).
  have Hsegment101d4 : IslaInstructionSegment state101d4 observations101d4 after.
  { rewrite <- Hbefore. apply (proj1 (segment_101d4_mstatus _ _ _ Hpc Hx15
      Hcode Hnext Hmstatus)). }
  exists observations94, state98, observations98, state9c, observations9c,
    statea0, observationsa0, statea4, observationsa4, state101d4,
    observations101d4, after.
  repeat split; try assumption.
  - unfold after, writeSuccess101d4After, writeSuccess15694Local. cbn.
    eapply writeSuccess101d4RegsDom; eassumption.
  - have HpcBefore : writeSuccessWithdrawalsConcretePc (state101d4, state.2) =
        Some 0x101d4.
    { rewrite <- Hbefore. unfold writeSuccessWithdrawalsConcretePc. cbn.
      rewrite Hpc. reflexivity. }
    have HpcAfter : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x101d8.
    { unfold after, writeSuccessWithdrawalsConcretePc,
        writeSuccess101d4After, writeSuccess15694Local,
        writeSuccess101d4Regs. cbn.
      rewrite lookup_insert writeSuccess101d4NextPcExact. reflexivity. }
    have Hx15After : after.1.(seq_regs) !! "x15" =
        Some (RVal_Bits (BV 64 0)).
    { unfold after, writeSuccess101d4After, writeSuccess15694Local,
        writeSuccess101d4Regs. cbn.
      rewrite lookup_insert_ne; try discriminate. rewrite lookup_insert.
      reflexivity. }
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold after, writeSuccess101d4After, writeSuccess15694Local. cbn.
      rewrite writeSuccess101d4RegsLookupOther; try discriminate. exact Hx9. }
    rewrite (rank_15694_at_101d4 (state101d4, state.2) remaining HpcBefore Hx9
      Hrange).
    rewrite (rank_15694_at_101d8_zero (after, state.2) remaining HpcAfter
      Hx15After Hx9After Hrange). lia.
Qed.

Lemma writeSuccessWithdrawalsEverySegment101d4Decreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations94 state98
    observations98 state9c observations9c statea0 observationsa0 statea4
    observationsa4 state101d4 observations101d4 after :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  IslaInstructionSegment state.1 observations94 state98 ->
  IslaInstructionSegment state98 observations98 state9c ->
  IslaInstructionSegment state9c observations9c statea0 ->
  IslaInstructionSegment statea0 observationsa0 statea4 ->
  IslaInstructionSegment statea4 observationsa4 state101d4 ->
  IslaInstructionSegment state101d4 observations101d4 after ->
  after = writeSuccess101d4After state101d4.1.(seq_regs) state101d4.2 /\
  dom after.1.(seq_regs) = dom state101d4.1.(seq_regs) /\
  rank_15694 (after, state.2) < rank_15694 (state101d4, state.2).
Proof.
  intros Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0 Hsegmenta4
    Hsegment101d4.
  destruct (writeSuccessWithdrawals101d4Context args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations94
    state98 observations98 state9c observations9c statea0 observationsa0 statea4
    observationsa4 state101d4 Hinv Hsegment94 Hsegment98 Hsegment9c Hsegmenta0
    Hsegmenta4) as
    (oldX15 & Hbefore & Hpc & Hx15 & Hcode & Hnext & Hmstatus & Hx9 & Hrange).
  have Hcanonical : IslaInstructionSegment
      (writeSuccess101d4Before state101d4.1.(seq_regs) state101d4.2)
      observations101d4 after.
  { rewrite Hbefore. exact Hsegment101d4. }
  have Hafter : after =
      writeSuccess101d4After state101d4.1.(seq_regs) state101d4.2.
  { exact (proj1 (segment_101d4_mstatus_covered _ _ _ _ _ Hpc Hx15 Hcode
      Hnext Hmstatus Hcanonical)). }
  split; first exact Hafter. split.
  - rewrite Hafter. unfold writeSuccess101d4After, writeSuccess15694Local. cbn.
    eapply writeSuccess101d4RegsDom; eassumption.
  - have HpcBefore : writeSuccessWithdrawalsConcretePc (state101d4, state.2) =
        Some 0x101d4.
    { rewrite <- Hbefore. unfold writeSuccessWithdrawalsConcretePc. cbn.
      rewrite Hpc. reflexivity. }
    have HpcAfter : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x101d8.
    { rewrite Hafter. unfold writeSuccessWithdrawalsConcretePc,
        writeSuccess101d4After, writeSuccess15694Local,
        writeSuccess101d4Regs. cbn.
      rewrite lookup_insert writeSuccess101d4NextPcExact. reflexivity. }
    have Hx15After : after.1.(seq_regs) !! "x15" =
        Some (RVal_Bits (BV 64 0)).
    { rewrite Hafter. unfold writeSuccess101d4After, writeSuccess15694Local,
        writeSuccess101d4Regs. cbn.
      rewrite lookup_insert_ne; try discriminate. rewrite lookup_insert.
      reflexivity. }
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { rewrite Hafter. unfold writeSuccess101d4After,
        writeSuccess15694Local. cbn.
      rewrite writeSuccess101d4RegsLookupOther; try discriminate. exact Hx9. }
    rewrite (rank_15694_at_101d4 (state101d4, state.2) remaining HpcBefore Hx9
      Hrange).
    rewrite (rank_15694_at_101d8_zero (after, state.2) remaining HpcAfter
      Hx15After Hx9After Hrange). lia.
Qed.

Print Assumptions writeSuccessWithdrawalsSegment101d4ExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment101d4Decreases.
