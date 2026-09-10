From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c0.
Require Import IslaTraces.write_success_93.a156c4.
Require Import IslaTraces.write_success_93.a156c8.
Require Import IslaTraces.write_success_93.a156cc.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c8Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156cc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ccCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.

Lemma writeSuccessWithdrawals156c0OutputPositionsDirect regs global
    (data : bv 64) priorLog oldX11 oldX10 oldX1 segments after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c0)) ->
  regs !! "x11" = Some oldX11 ->
  regs !! "x18" = Some (RVal_Bits data) ->
  regs !! "x10" = Some oldX10 ->
  regs !! "x1" = Some oldX1 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  writeSuccessWithdrawalsInstructionTable global ->
  WriteSuccessWithdrawalsRecordedRun 4
    (writeSuccess156c0Before regs global, priorLog) segments after ->
  let r1 := writeSuccess156c0Regs regs in
  let r2 := writeSuccess156c4Regs r1 data in
  let r3 := writeSuccess156c8Regs r2 in
  exists observations0 observations1 observations2 observations3,
    segments = [observations0; observations1; observations2; observations3] /\
    after = (writeSuccess156ccAfter r3 global, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess156c0Before regs global, priorLog) [observations0]
      (writeSuccess156c4Before r1 global, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess156c4Before r1 global, priorLog) [observations1]
      (writeSuccess156c8Before r2 global, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess156c8Before r2 global, priorLog) [observations2]
      (writeSuccess156ccBefore r3 global, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess156ccBefore r3 global, priorLog) [observations3] after.
Proof.
  intros Hpc Hx11 Hx18 Hx10 Hx1 Hmstatus Htable Hrecorded.
  cbn.
  destruct Hrecorded as (Hrun & Hlog).
  have Hc0 := Htable 0x156c0 a156c0 ltac:(cbn; tauto).
  have Hc4 := Htable 0x156c4 a156c4 ltac:(cbn; tauto).
  have Hc8 := Htable 0x156c8 a156c8 ltac:(cbn; tauto).
  have Hcc := Htable 0x156cc a156cc ltac:(cbn; tauto).
  have Hout := Htable 0x10190 a10190 ltac:(cbn; tauto).
  inversion Hrun as [|? ? o0 s1 gs1 z1 Hs0 Hr1]; subst.
  inversion Hr1 as [|? ? o1 s2 gs2 z2 Hs1 Hr2]; subst.
  inversion Hr2 as [|? ? o2 s3 gs3 z3 Hs2 Hr3]; subst.
  inversion Hr3 as [|? ? o3 s4 gs4 z4 Hs3 Hr4]; subst.
  set (r1 := writeSuccess156c0Regs regs).
  destruct (segment_156c0_mstatus_covered regs global oldX11 o0 s1 Hpc Hx11
    Hc0 Hc4 Hmstatus Hs0) as (Hs1eq & Ho0). subst s1 o0.
  have Hpc1 : r1 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c4)).
  { unfold r1, writeSuccess156c0Regs. rewrite lookup_insert.
    rewrite writeSuccess156c0NextPcExact. reflexivity. }
  have Hx18_1 : r1 !! "x18" = Some (RVal_Bits data).
  { unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx18. }
  have Hx10_1 : r1 !! "x10" = Some oldX10.
  { unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx10. }
  have Hm1 : eval_a_exp r1 writeSuccess156c4Mstatus = Some (Val_Bool true).
  { unfold r1, writeSuccess156c0Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hmstatus. }
  set (r2 := writeSuccess156c4Regs r1 data).
  destruct (segment_156c4_mstatus_covered r1 global data oldX10 o1 s2 Hpc1
    Hx18_1 Hx10_1 Hc4 Hc8 Hm1 Hs1) as (Hs2eq & Ho1). subst s2 o1.
  have Hpc2 : r2 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c8)).
  { unfold r2, writeSuccess156c4Regs. rewrite lookup_insert.
    rewrite writeSuccess156c4NextPcExact. reflexivity. }
  have Hx1_2 : r2 !! "x1" = Some oldX1.
  { unfold r2. rewrite writeSuccess156c4RegsLookupOther; try discriminate.
    unfold r1. rewrite writeSuccess156c0RegsLookupOther; try discriminate.
    exact Hx1. }
  have Hm2 : eval_a_exp r2 writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold r2, writeSuccess156c4Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hm1. }
  set (r3 := writeSuccess156c8Regs r2).
  destruct (segment_156c8_mstatus_covered r2 global oldX1 o2 s3 Hpc2 Hx1_2
    Hc8 Hcc Hm2 Hs2) as (Hs3eq & Ho2). subst s3 o2.
  have Hpc3 : r3 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156cc)).
  { unfold r3, writeSuccess156c8Regs. rewrite lookup_insert.
    rewrite writeSuccess156c8NextPcExact. reflexivity. }
  have Hx1_3 : r3 !! "x1" = Some (RVal_Bits writeSuccess156ccRa).
  { unfold r3, writeSuccess156c8Regs. rewrite lookup_insert_ne;
      last discriminate. rewrite lookup_insert. reflexivity. }
  have Hm3 : eval_a_exp r3 writeSuccess15694Mstatus = Some (Val_Bool true).
  { unfold r3, writeSuccess156c8Regs. cbn.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert_ne; last discriminate. exact Hm2. }
  destruct (segment_156cc_mstatus_covered r3 global o3 s4 Hpc3 Hx1_3 Hcc
    Hout Hm3 Hs3) as (Hs4eq & Ho3). subst o3.
  have Htail : gs4 = [] by (inversion Hr4; reflexivity).
  have Hmachine : s4 = after.1 by (inversion Hr4; reflexivity).
  rewrite Hs4eq in Hmachine.
  have Hsilent0 : concat (map microLabels
      (writeSuccess156c0Observations regs global)) = [].
  { unfold writeSuccess156c0Observations,
      writeSuccess156c0PrefixObservations. reflexivity. }
  have Hsilent1 : concat (map microLabels
      (writeSuccess156c4Observations r1 global data)) = [].
  { unfold writeSuccess156c4Observations,
      writeSuccess156c4PrefixObservations. reflexivity. }
  have Hsilent2 : concat (map microLabels
      (writeSuccess156c8Observations r2 global)) = [].
  { unfold writeSuccess156c8Observations,
      writeSuccess156c8PrefixObservations. reflexivity. }
  have Hsilent3 : concat (map microLabels
      (writeSuccess156ccObservations r3 global)) = [].
  { unfold writeSuccess156ccObservations,
      writeSuccess156ccPrefixObservations. reflexivity. }
  have Hseg0 : IslaInstructionSegment (writeSuccess156c0Before regs global)
      (writeSuccess156c0Observations regs global)
      (writeSuccess156c4Before r1 global).
  { unfold r1, writeSuccess156c4Before. exact Hs0. }
  have Hseg1 : IslaInstructionSegment (writeSuccess156c4Before r1 global)
      (writeSuccess156c4Observations r1 global data)
      (writeSuccess156c8Before r2 global).
  { unfold r2, writeSuccess156c8Before. exact Hs1. }
  have Hseg2 : IslaInstructionSegment (writeSuccess156c8Before r2 global)
      (writeSuccess156c8Observations r2 global)
      (writeSuccess156ccBefore r3 global).
  { unfold r3, writeSuccess156ccBefore. exact Hs2. }
  have Hseg3 : IslaInstructionSegment (writeSuccess156ccBefore r3 global)
      (writeSuccess156ccObservations r3 global)
      (writeSuccess156ccAfter r3 global).
  { rewrite <- Hs4eq. exact Hs3. }
  destruct after as [afterMachine afterLog]. cbn in Hmachine, Hlog |- *.
  subst afterMachine.
  rewrite Htail in Hlog.
  unfold writeSuccess156c0Observations, writeSuccess156c0PrefixObservations,
    writeSuccess156c4Observations, writeSuccess156c4PrefixObservations,
    writeSuccess156c8Observations, writeSuccess156c8PrefixObservations,
    writeSuccess156ccObservations, writeSuccess156ccPrefixObservations in Hlog.
  cbn [flattenMicroObservations segmentRecords segmentRecordsFrom] in Hlog.
  rewrite app_nil_r in Hlog. subst afterLog.
  exists (writeSuccess156c0Observations regs global),
    (writeSuccess156c4Observations r1 global data),
    (writeSuccess156c8Observations r2 global),
    (writeSuccess156ccObservations r3 global).
  split; first (rewrite Htail; reflexivity).
  split; first reflexivity.
  split.
  - eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
      (writeSuccess156c0Before regs global, priorLog) []
      (writeSuccess156c0Before regs global, priorLog)
      (writeSuccess156c0Observations regs global)
      (writeSuccess156c4Before r1 global)).
    + apply writeSuccessWithdrawalsRecordedRunZero.
    + exact Hseg0.
    + exact Hsilent0.
  - split.
    + eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
        (writeSuccess156c4Before r1 global, priorLog) []
        (writeSuccess156c4Before r1 global, priorLog)
        (writeSuccess156c4Observations r1 global data)
        (writeSuccess156c8Before r2 global)).
      * apply writeSuccessWithdrawalsRecordedRunZero.
      * exact Hseg1.
      * exact Hsilent1.
    + split.
      * eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
          (writeSuccess156c8Before r2 global, priorLog) []
          (writeSuccess156c8Before r2 global, priorLog)
          (writeSuccess156c8Observations r2 global)
          (writeSuccess156ccBefore r3 global)).
        -- apply writeSuccessWithdrawalsRecordedRunZero.
        -- exact Hseg2.
        -- exact Hsilent2.
      * eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
          (writeSuccess156ccBefore r3 global, priorLog) []
          (writeSuccess156ccBefore r3 global, priorLog)
          (writeSuccess156ccObservations r3 global)
          (writeSuccess156ccAfter r3 global)).
        -- apply writeSuccessWithdrawalsRecordedRunZero.
        -- exact Hseg3.
        -- exact Hsilent3.
Qed.

Lemma writeSuccessWithdrawals156c0OutputPositionsExact args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  WriteSuccessWithdrawalsRecordedRun 4
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal,
     writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
       withdrawal) segments after ->
  let entry := writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
    withdrawal in
  let data := (sp + BV 64 1768)%bv in
  let r1 := writeSuccess156c0Regs entry.1.(seq_regs) in
  let r2 := writeSuccess156c4Regs r1 data in
  let r3 := writeSuccess156c8Regs r2 in
  exists observations0 observations1 observations2 observations3,
    segments = [observations0; observations1; observations2; observations3] /\
    after = (writeSuccessWithdrawalsOutputEntry entry.1.(seq_regs) entry.2 data,
      writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
        withdrawal) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (entry, writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2
        sp withdrawal) [observations0]
      (writeSuccess156c4Before r1 entry.2,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess156c4Before r1 entry.2,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) [observations1]
      (writeSuccess156c8Before r2 entry.2,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess156c8Before r2 entry.2,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) [observations2]
      (writeSuccess156ccBefore r3 entry.2,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccess156ccBefore r3 entry.2,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) [observations3] after.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Hrun.
  cbn.
  destruct (writeSuccessWithdrawalsSecondEncoderEndpointDirectFacts args sp
    pointer base total processed remaining withdrawal allBytes prefix current
    suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0
    global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2) as
    (x11 & x10 & x1 & Hpc & Hx11 & Hx18 & Hx10 & Hx1 & Hm & Htable).
  rewrite (writeSuccessWithdrawalsSecondEncoderEndpointBefore args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2) in Hrun |- *.
  pose proof (writeSuccessWithdrawals156c0OutputPositionsDirect
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
      withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
      withdrawal).2 (sp + BV 64 1768)%bv
    (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
      withdrawal) x11 x10 x1 segments after Hpc Hx11 Hx18 Hx10 Hx1 Hm Htable
    Hrun) as Hpositions.
  unfold writeSuccessWithdrawalsOutputEntry.
  exact Hpositions.
Qed.

Print Assumptions writeSuccessWithdrawals156c0OutputPositionsDirect.
Print Assumptions writeSuccessWithdrawals156c0OutputPositionsExact.
