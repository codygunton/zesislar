From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_90.a15698.
Require Import IslaTraces.write_success_90.a1569c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsInv15694Entry args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists oldX10,
    state.1 = writeSuccess15694Before state.1.1.(seq_regs) state.1.2 /\
    state.1.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15694)) /\
    state.1.1.(seq_regs) !! "x10" = Some oldX10 /\
    (exists oldX12, state.1.1.(seq_regs) !! "x12" = Some oldX12) /\
    state.1.2.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 /\
    state.1.2.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 /\
    writeSuccessTraceAssumptions
      (writeSuccess15694Before state.1.1.(seq_regs) state.1.2).
Proof.
  intros Hinv.
  have Hboundary : IslaInstructionBoundary state.1 by
    (unfold Inv_15694 in Hinv; tauto).
  have HpcReg : state.1.1.(seq_pc_reg) = "PC" by
    (unfold Inv_15694 in Hinv; tauto).
  have Hpc : writeSuccessWithdrawalsConcretePc state = Some 0x15694 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx10 : exists oldX10,
      state.1.1.(seq_regs) !! "x10" = Some oldX10 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx12 : exists oldX12,
      state.1.1.(seq_regs) !! "x12" = Some oldX12 by
    (unfold Inv_15694 in Hinv; tauto).
  have Htable : writeSuccessWithdrawalsInstructionTable state.1.2 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hassumptions : writeSuccessTraceAssumptions state.1 by
    (unfold Inv_15694 in Hinv; tauto).
  destruct state as [[[trace regs pcReg nb] global] log]. cbn in *.
  subst pcReg.
  destruct Hboundary as [Hnb (pc & instruction & HpcLookup & Hcode & Htrace)].
  cbn in Hnb, Htrace.
  have HpcUnsigned : bv_unsigned pc = 0x15694.
  { unfold writeSuccessWithdrawalsConcretePc in Hpc. cbn in Hpc.
    rewrite HpcLookup in Hpc. inversion Hpc. reflexivity. }
  have HpcBits : pc = Z_to_bv 64 0x15694.
  { apply bv_eq. rewrite Z_to_bv_unsigned. cbn. exact HpcUnsigned. }
  have HpcExact : regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15694)).
  { rewrite HpcBits in HpcLookup. exact HpcLookup. }
  have Hcode15694 : global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode15698 : global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  rewrite HpcBits Hcode15694 in Hcode. inversion Hcode. subst instruction.
  have Hentry :
      ({| seq_trace := trace; seq_regs := regs; seq_pc_reg := "PC";
          seq_nb_state := nb |}, global) =
        writeSuccess15694Before regs global.
  { unfold writeSuccess15694Before, writeSuccess15694Local.
    rewrite Hnb. rewrite <- H0. reflexivity. }
  destruct Hx10 as [oldX10 Hx10]. exists oldX10.
  repeat split; try assumption.
Qed.

Lemma writeSuccess15694RegsDom regs sp oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) ->
  regs !! "x10" = Some oldX10 ->
  dom (writeSuccess15694Regs regs sp) = dom regs.
Proof.
  intros Hpc Hx10.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx10.
  unfold writeSuccess15694Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Lemma writeSuccess15694MstatusPreserved regs sp :
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp (writeSuccess15694Regs regs sp) writeSuccess15694Mstatus =
    Some (Val_Bool true).
Proof.
  intros Hmstatus. unfold writeSuccess15694Regs, writeSuccess15694Mstatus in *.
  cbn in *. rewrite !lookup_insert_ne; try discriminate. exact Hmstatus.
Qed.

Lemma writeSuccessWithdrawalsPhase1569c state :
  writeSuccessWithdrawalsConcretePc state = Some 0x1569c ->
  writeSuccessWithdrawalsPhaseRemaining state = 408%nat.
Proof.
  intros Hpc. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. vm_compute. reflexivity.
Qed.

Lemma rank_15694_at_1569c state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x1569c ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 408)%nat.
Proof.
  intros Hpc Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase1569c state Hpc.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 408 =
    410 * remaining + 408)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsSegment15694ExistsAndDecreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists observations after,
    IslaInstructionSegment state.1 observations after /\
    dom after.1.(seq_regs) = dom state.1.1.(seq_regs) /\
    after.1.(seq_regs) !! "x12" = state.1.1.(seq_regs) !! "x12" /\
    rank_15694 (after, state.2) < rank_15694 state.
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsInv15694Entry args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (oldX10 & Hentry & Hpc & Hx10 & Hx12 & Hcode & Hnext & Hassumptions).
  have Hsp : state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) by
    (unfold Inv_15694 in Hinv; tauto).
  have HrankBefore := Inv_15694_rank _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinv.
  have Hrange := Inv_15694_counter_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinv.
  pose (observations := writeSuccess15694Observations
    state.1.1.(seq_regs) state.1.2 sp).
  pose (after := writeSuccess15694After state.1.1.(seq_regs) state.1.2 sp).
  have Hsegment : IslaInstructionSegment state.1 observations after.
  { rewrite Hentry. apply (proj1 (segment_15694 _ _ _ _ Hpc Hsp Hx10 Hcode
      Hnext Hassumptions)). }
  exists observations, after. split; first exact Hsegment. split.
  - unfold after, writeSuccess15694After, writeSuccess15694Local. cbn.
    eapply writeSuccess15694RegsDom; eassumption.
  - split.
    + unfold after, writeSuccess15694After, writeSuccess15694Local. cbn.
      apply writeSuccess15694RegsLookupOther; discriminate.
    + have HpcAfter : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x15698.
    { unfold after, writeSuccessWithdrawalsConcretePc, writeSuccess15694After,
        writeSuccess15694Local, writeSuccess15694Regs. cbn.
      rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
    have Hx9 : state.1.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
      (unfold Inv_15694 in Hinv; tauto).
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold after, writeSuccess15694After, writeSuccess15694Local,
        writeSuccess15694Regs. cbn.
      rewrite !lookup_insert_ne; try discriminate. exact Hx9. }
    rewrite HrankBefore.
    rewrite (rank_15694_at_15698 (after, state.2) remaining HpcAfter Hx9After
      Hrange). lia.
Qed.

Lemma writeSuccessWithdrawalsEverySegment15694Decreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations after :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  IslaInstructionSegment state.1 observations after ->
  after = writeSuccess15694After state.1.1.(seq_regs) state.1.2 sp /\
  dom after.1.(seq_regs) = dom state.1.1.(seq_regs) /\
  after.1.(seq_regs) !! "x12" = state.1.1.(seq_regs) !! "x12" /\
  rank_15694 (after, state.2) < rank_15694 state.
Proof.
  intros Hinv Hsegment.
  destruct (writeSuccessWithdrawalsInv15694Entry args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (oldX10 & Hentry & Hpc & Hx10 & Hx12 & Hcode & Hnext & Hassumptions).
  have Hsp : state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hcovered :
      after = writeSuccess15694After state.1.1.(seq_regs) state.1.2 sp.
  { have HsegmentCanonical : IslaInstructionSegment
        (writeSuccess15694Before state.1.1.(seq_regs) state.1.2)
        observations after.
    { rewrite <- Hentry. exact Hsegment. }
    exact (proj1 (segment_15694_covered _ _ _ _ _ _ Hpc Hsp Hx10 Hcode Hnext
      Hassumptions HsegmentCanonical)). }
  split; first exact Hcovered. split.
  - rewrite Hcovered. unfold writeSuccess15694After, writeSuccess15694Local. cbn.
    eapply writeSuccess15694RegsDom; eassumption.
  - split.
    + rewrite Hcovered. unfold writeSuccess15694After,
        writeSuccess15694Local. cbn.
      apply writeSuccess15694RegsLookupOther; discriminate.
    + have HrankBefore := Inv_15694_rank _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hinv.
    have Hrange := Inv_15694_counter_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hinv.
    have Hx9 : state.1.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
      (unfold Inv_15694 in Hinv; tauto).
    have HpcAfter : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x15698.
    { rewrite Hcovered. unfold writeSuccessWithdrawalsConcretePc,
        writeSuccess15694After, writeSuccess15694Local,
        writeSuccess15694Regs. cbn.
      rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { rewrite Hcovered. unfold writeSuccess15694After,
        writeSuccess15694Local, writeSuccess15694Regs. cbn.
      rewrite !lookup_insert_ne; try discriminate. exact Hx9. }
    rewrite HrankBefore.
    rewrite (rank_15694_at_15698 (after, state.2) remaining HpcAfter Hx9After
      Hrange). lia.
Qed.

Lemma writeSuccessWithdrawalsSegment15698ExistsAndDecreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists observations94 middle observations98 after,
    IslaInstructionSegment state.1 observations94 middle /\
    IslaInstructionSegment middle observations98 after /\
    dom after.1.(seq_regs) = dom middle.1.(seq_regs) /\
    rank_15694 (after, state.2) < rank_15694 (middle, state.2).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsInv15694Entry args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (oldX10 & Hentry & Hpc94 & Hx10 & Hx12 & Hcode94 & Hcode98 & Hassumptions).
  destruct Hx12 as [oldX12 Hx12].
  have Hsp : state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) by
    (unfold Inv_15694 in Hinv; tauto).
  have Htable : writeSuccessWithdrawalsInstructionTable state.1.2 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hcode9c : state.1.2.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hrange := Inv_15694_counter_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinv.
  have Hx9 : state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hmstatus := writeSuccess15694MstatusFromTraceAssumptions
    state.1.1.(seq_regs) state.1.2 Hassumptions.
  pose (observations94 := writeSuccess15694Observations
    state.1.1.(seq_regs) state.1.2 sp).
  pose (middle := writeSuccess15694After state.1.1.(seq_regs) state.1.2 sp).
  have Hsegment94 : IslaInstructionSegment state.1 observations94 middle.
  { rewrite Hentry. apply (proj1 (segment_15694 _ _ _ _ Hpc94 Hsp Hx10 Hcode94
      Hcode98 Hassumptions)). }
  have Hpc98 : middle.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15698)).
  { unfold middle, writeSuccess15694After, writeSuccess15694Local,
      writeSuccess15694Regs. cbn.
    rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
  have Hx12Middle : middle.1.(seq_regs) !! "x12" = Some oldX12.
  { unfold middle, writeSuccess15694After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx12. }
  have HmstatusMiddle :
      eval_a_exp middle.1.(seq_regs) writeSuccess15694Mstatus =
        Some (Val_Bool true).
  { unfold middle, writeSuccess15694After, writeSuccess15694Local. cbn.
    exact (writeSuccess15694MstatusPreserved _ _ Hmstatus). }
  pose (observations98 := writeSuccess15698Observations
    middle.1.(seq_regs) middle.2).
  pose (after := writeSuccess15698After middle.1.(seq_regs) middle.2).
  have Hsegment98 : IslaInstructionSegment middle observations98 after.
  { apply (proj1 (segment_15698_mstatus _ _ _ Hpc98 Hx12Middle Hcode98
      Hcode9c HmstatusMiddle)). }
  exists observations94, middle, observations98, after.
  split; first exact Hsegment94. split; first exact Hsegment98. split.
  - unfold after, writeSuccess15698After, writeSuccess15694Local. cbn.
    eapply writeSuccess15698RegsDom; eassumption.
  - have HpcMiddle : writeSuccessWithdrawalsConcretePc (middle, state.2) =
        Some 0x15698.
    { unfold middle, writeSuccessWithdrawalsConcretePc,
        writeSuccess15694After, writeSuccess15694Local,
        writeSuccess15694Regs. cbn.
      rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
    have Hx9Middle : middle.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold middle, writeSuccess15694After, writeSuccess15694Local. cbn.
      rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx9. }
    have HpcAfter : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x1569c.
    { unfold after, writeSuccessWithdrawalsConcretePc,
        writeSuccess15698After, writeSuccess15694Local,
        writeSuccess15698Regs. cbn.
      rewrite lookup_insert writeSuccess15698NextPcExact. reflexivity. }
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { unfold after, writeSuccess15698After, writeSuccess15694Local. cbn.
      rewrite writeSuccess15698RegsLookupOther; try discriminate.
      exact Hx9Middle. }
    rewrite (rank_15694_at_15698 (middle, state.2) remaining HpcMiddle Hx9Middle
      Hrange).
    rewrite (rank_15694_at_1569c (after, state.2) remaining HpcAfter Hx9After
      Hrange). lia.
Qed.

Lemma writeSuccessWithdrawalsEverySegment15698Decreases args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state observations94 middle
    observations98 after :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  IslaInstructionSegment state.1 observations94 middle ->
  IslaInstructionSegment middle observations98 after ->
  after = writeSuccess15698After middle.1.(seq_regs) middle.2 /\
  dom after.1.(seq_regs) = dom middle.1.(seq_regs) /\
  rank_15694 (after, state.2) < rank_15694 (middle, state.2).
Proof.
  intros Hinv Hsegment94 Hsegment98.
  destruct (writeSuccessWithdrawalsInv15694Entry args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (oldX10 & Hentry & Hpc94 & Hx10 & Hx12 & Hcode94 & Hcode98 & Hassumptions).
  destruct Hx12 as [oldX12 Hx12].
  have Hsp : state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) by
    (unfold Inv_15694 in Hinv; tauto).
  have Htable : writeSuccessWithdrawalsInstructionTable state.1.2 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hcode9c : state.1.2.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hsegment94Canonical : IslaInstructionSegment
      (writeSuccess15694Before state.1.1.(seq_regs) state.1.2)
      observations94 middle.
  { rewrite <- Hentry. exact Hsegment94. }
  have Hmiddle :
      middle = writeSuccess15694After state.1.1.(seq_regs) state.1.2 sp.
  { exact (proj1 (segment_15694_covered _ _ _ _ _ _ Hpc94 Hsp Hx10 Hcode94
      Hcode98 Hassumptions Hsegment94Canonical)). }
  have Hpc98 : middle.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15698)).
  { rewrite Hmiddle. unfold writeSuccess15694After, writeSuccess15694Local,
      writeSuccess15694Regs. cbn.
    rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
  have Hx12Middle : middle.1.(seq_regs) !! "x12" = Some oldX12.
  { rewrite Hmiddle. unfold writeSuccess15694After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx12. }
  have Hmstatus := writeSuccess15694MstatusFromTraceAssumptions
    state.1.1.(seq_regs) state.1.2 Hassumptions.
  have HmstatusMiddle :
      eval_a_exp middle.1.(seq_regs) writeSuccess15694Mstatus =
        Some (Val_Bool true).
  { rewrite Hmiddle. unfold writeSuccess15694After, writeSuccess15694Local. cbn.
    exact (writeSuccess15694MstatusPreserved _ _ Hmstatus). }
  have Hcode98Middle : middle.2.(seq_instrs) !! Z_to_bv 64 0x15698 =
      Some a15698.
  { rewrite Hmiddle. exact Hcode98. }
  have Hcode9cMiddle : middle.2.(seq_instrs) !! Z_to_bv 64 0x1569c =
      Some a1569c.
  { rewrite Hmiddle. exact Hcode9c. }
  have Hsegment98Canonical : IslaInstructionSegment
      (writeSuccess15698Before middle.1.(seq_regs) middle.2)
      observations98 after.
  { have Hbefore98 :
        writeSuccess15698Before middle.1.(seq_regs) middle.2 = middle.
    { rewrite Hmiddle. reflexivity. }
    rewrite Hbefore98. exact Hsegment98. }
  have Hafter : after = writeSuccess15698After middle.1.(seq_regs) middle.2.
  { apply (proj1 (segment_15698_mstatus_covered _ _ _ _ _ Hpc98 Hx12Middle
      Hcode98Middle Hcode9cMiddle HmstatusMiddle Hsegment98Canonical)). }
  split; first exact Hafter. split.
  - rewrite Hafter. unfold writeSuccess15698After, writeSuccess15694Local. cbn.
    eapply writeSuccess15698RegsDom; eassumption.
  - have Hrange := Inv_15694_counter_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hinv.
    have Hx9 : state.1.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
      (unfold Inv_15694 in Hinv; tauto).
    have HpcMiddle : writeSuccessWithdrawalsConcretePc (middle, state.2) =
        Some 0x15698.
    { rewrite Hmiddle. unfold writeSuccessWithdrawalsConcretePc,
        writeSuccess15694After, writeSuccess15694Local,
        writeSuccess15694Regs. cbn.
      rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
    have Hx9Middle : middle.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { rewrite Hmiddle. unfold writeSuccess15694After,
        writeSuccess15694Local. cbn.
      rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx9. }
    have HpcAfter : writeSuccessWithdrawalsConcretePc (after, state.2) =
        Some 0x1569c.
    { rewrite Hafter. unfold writeSuccessWithdrawalsConcretePc,
        writeSuccess15698After, writeSuccess15694Local,
        writeSuccess15698Regs. cbn.
      rewrite lookup_insert writeSuccess15698NextPcExact. reflexivity. }
    have Hx9After : after.1.(seq_regs) !! "x9" =
        Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))).
    { rewrite Hafter. unfold writeSuccess15698After,
        writeSuccess15694Local. cbn.
      rewrite writeSuccess15698RegsLookupOther; try discriminate.
      exact Hx9Middle. }
    rewrite (rank_15694_at_15698 (middle, state.2) remaining HpcMiddle Hx9Middle
      Hrange).
    rewrite (rank_15694_at_1569c (after, state.2) remaining HpcAfter Hx9After
      Hrange). lia.
Qed.

Print Assumptions writeSuccessWithdrawalsInv15694Entry.
Print Assumptions writeSuccess15694RegsDom.
Print Assumptions writeSuccessWithdrawalsSegment15694ExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment15694Decreases.
Print Assumptions writeSuccess15694MstatusPreserved.
Print Assumptions writeSuccessWithdrawalsPhase1569c.
Print Assumptions rank_15694_at_1569c.
Print Assumptions writeSuccessWithdrawalsSegment15698ExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment15698Decreases.
