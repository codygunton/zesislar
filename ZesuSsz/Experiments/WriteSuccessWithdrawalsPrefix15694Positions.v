From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_90.a15698.
Require Import IslaTraces.write_success_90.a1569c.
Require Import IslaTraces.write_success_90.a156a0.
Require Import IslaTraces.write_success_90.a156a4.
Require Import IslaTraces.write_success_02.a101d4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569cCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefix15694PositionsExact args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state segments after :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 5 state segments after ->
  exists observations0 observations1 observations2 observations3 observations4,
    segments = [observations0; observations1; observations2; observations3;
      observations4] /\
    after = (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1 state [observations0]
      (writeSuccessWithdrawalsPrefixState98 state.1 sp, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawalsPrefixState98 state.1 sp, priorLog)
      [observations1]
      (writeSuccessWithdrawalsPrefixState9c state.1 sp, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawalsPrefixState9c state.1 sp, priorLog)
      [observations2]
      (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer, priorLog)
      [observations3]
      (writeSuccessWithdrawalsPrefixStatea4 state.1 sp pointer, priorLog) /\
    WriteSuccessWithdrawalsRecordedRun 1
      (writeSuccessWithdrawalsPrefixStatea4 state.1 sp pointer, priorLog)
      [observations4]
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, priorLog).
Proof.
  intros Hinv [Hrun Hlog].
  destruct (writeSuccessWithdrawalsInv15694DirectEntry args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state Hinv) as
    (oldX1 & oldX10 & oldX11 & oldX12 & Hentry & Hpc & Hx1 & Hsp & Hpointer &
     Hx10 & Hx11 & Hx12 & Htable & Hmstatus).
  have HstateLog : state.2 = priorLog by (unfold Inv_15694 in Hinv; tauto).
  have Hcode94 := Htable 0x15694 a15694 ltac:(cbn; tauto).
  have Hcode98 := Htable 0x15698 a15698 ltac:(cbn; tauto).
  have Hcode9c := Htable 0x1569c a1569c ltac:(cbn; tauto).
  have Hcodea0 := Htable 0x156a0 a156a0 ltac:(cbn; tauto).
  have Hcodea4 := Htable 0x156a4 a156a4 ltac:(cbn; tauto).
  have Hcode101d4 := Htable 0x101d4 a101d4 ltac:(cbn; tauto).
  inversion Hrun as
    [|? ? observations0 middle0 segments0 machineAfter0 Hseg0 Hrun0]; subst.
  inversion Hrun0 as
    [|? ? observations1 middle1 segments1 machineAfter1 Hseg1 Hrun1]; subst.
  inversion Hrun1 as
    [|? ? observations2 middle2 segments2 machineAfter2 Hseg2 Hrun2]; subst.
  inversion Hrun2 as
    [|? ? observations3 middle3 segments3 machineAfter3 Hseg3 Hrun3]; subst.
  inversion Hrun3 as
    [|? ? observations4 middle4 segments4 machineAfter4 Hseg4 Hrun4]; subst.
  destruct (segment_15694_mstatus_covered state.1.1.(seq_regs) state.1.2 sp
    oldX10 observations0 middle0 Hpc Hsp Hx10 Hcode94 Hcode98 Hmstatus
    ltac:(rewrite <- Hentry; exact Hseg0)) as (Hmiddle0 & Hobs0).
  subst middle0 observations0.
  set (s98 := writeSuccessWithdrawalsPrefixState98 state.1 sp).
  have Hpc98 : s98.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15698)).
  { unfold s98, writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
      writeSuccess15694Local, writeSuccess15694Regs. cbn.
    rewrite lookup_insert writeSuccess15694NextPcExact. reflexivity. }
  have Hx12_98 : s98.1.(seq_regs) !! "x12" = Some oldX12.
  { unfold s98, writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
      writeSuccess15694Local. cbn. rewrite writeSuccess15694RegsLookupOther;
      try discriminate. exact Hx12. }
  have Hmstatus98 : eval_a_exp s98.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold s98, writeSuccessWithdrawalsPrefixState98, writeSuccess15694After,
      writeSuccess15694Local, writeSuccess15694Regs,
      writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  destruct (segment_15698_mstatus_covered s98.1.(seq_regs) s98.2 oldX12
    observations1 middle1 Hpc98 Hx12_98 Hcode98 Hcode9c Hmstatus98 Hseg1)
    as (Hmiddle1 & Hobs1).
  subst middle1 observations1.
  set (s9c := writeSuccessWithdrawalsPrefixState9c state.1 sp).
  have Hpc9c : s9c.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x1569c)).
  { unfold s9c, writeSuccessWithdrawalsPrefixState9c, s98,
      writeSuccessWithdrawalsPrefixState98, writeSuccess15698After,
      writeSuccess15694Local, writeSuccess15698Regs. cbn.
    rewrite lookup_insert writeSuccess15698NextPcExact. reflexivity. }
  have Hx8_9c : s9c.1.(seq_regs) !! "x8" = Some (RVal_Bits pointer).
  { unfold s9c, writeSuccessWithdrawalsPrefixState9c, s98,
      writeSuccessWithdrawalsPrefixState98, writeSuccess15698After,
      writeSuccess15694After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hpointer. }
  have Hx11_9c : s9c.1.(seq_regs) !! "x11" = Some oldX11.
  { unfold s9c, writeSuccessWithdrawalsPrefixState9c, s98,
      writeSuccessWithdrawalsPrefixState98, writeSuccess15698After,
      writeSuccess15694After, writeSuccess15694Local. cbn.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx11. }
  have Hmstatus9c : eval_a_exp s9c.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold s9c, writeSuccessWithdrawalsPrefixState9c, s98,
      writeSuccessWithdrawalsPrefixState98, writeSuccess15698After,
      writeSuccess15694After, writeSuccess15694Local, writeSuccess15698Regs,
      writeSuccess15694Regs, writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  destruct (segment_1569c_mstatus_covered s9c.1.(seq_regs) s9c.2 pointer
    oldX11 observations2 middle2 Hpc9c Hx8_9c Hx11_9c Hcode9c Hcodea0
    Hmstatus9c Hseg2) as (Hmiddle2 & Hobs2).
  subst middle2 observations2.
  set (sa0 := writeSuccessWithdrawalsPrefixStatea0 state.1 sp pointer).
  have Hpca0 : sa0.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156a0)).
  { unfold sa0, writeSuccessWithdrawalsPrefixStatea0, s9c,
      writeSuccessWithdrawalsPrefixState9c, writeSuccess1569cAfter,
      writeSuccess1569cLocal, writeSuccess1569cRegs. cbn.
    rewrite lookup_insert writeSuccess1569cNextPcExact. reflexivity. }
  have Hx1_a0 : sa0.1.(seq_regs) !! "x1" = Some oldX1.
  { unfold sa0, writeSuccessWithdrawalsPrefixStatea0, s9c,
      writeSuccessWithdrawalsPrefixState9c, s98,
      writeSuccessWithdrawalsPrefixState98, writeSuccess1569cAfter,
      writeSuccess15698After, writeSuccess15694After, writeSuccess1569cLocal,
      writeSuccess15694Local. cbn.
    rewrite writeSuccess1569cRegsLookupOther; try discriminate.
    rewrite writeSuccess15698RegsLookupOther; try discriminate.
    rewrite writeSuccess15694RegsLookupOther; try discriminate. exact Hx1. }
  have Hmstatusa0 : eval_a_exp sa0.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold sa0, writeSuccessWithdrawalsPrefixStatea0, s9c,
      writeSuccessWithdrawalsPrefixState9c, s98,
      writeSuccessWithdrawalsPrefixState98, writeSuccess1569cAfter,
      writeSuccess15698After, writeSuccess15694After, writeSuccess1569cLocal,
      writeSuccess15694Local, writeSuccess1569cRegs, writeSuccess15698Regs,
      writeSuccess15694Regs, writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  destruct (segment_156a0_mstatus_covered sa0.1.(seq_regs) sa0.2 oldX1
    observations3 middle3 Hpca0 Hx1_a0 Hcodea0 Hcodea4 Hmstatusa0 Hseg3)
    as (Hmiddle3 & Hobs3).
  subst middle3 observations3.
  set (sa4 := writeSuccessWithdrawalsPrefixStatea4 state.1 sp pointer).
  have Hpca4 : sa4.1.(seq_regs) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156a4)).
  { unfold sa4, writeSuccessWithdrawalsPrefixStatea4, sa0,
      writeSuccessWithdrawalsPrefixStatea0, writeSuccess156a0After,
      writeSuccess15694Local, writeSuccess156a0Regs. cbn.
    rewrite lookup_insert writeSuccess156a0NextPcExact. reflexivity. }
  have Hx1_a4 : sa4.1.(seq_regs) !! "x1" =
      Some (RVal_Bits writeSuccess156a4Ra).
  { unfold sa4, writeSuccessWithdrawalsPrefixStatea4, sa0,
      writeSuccessWithdrawalsPrefixStatea0, writeSuccess156a0After,
      writeSuccess15694Local, writeSuccess156a0Regs, writeSuccess156a4Ra.
    cbn. rewrite lookup_insert_ne; try discriminate.
    rewrite lookup_insert. reflexivity. }
  have Hmstatusa4 : eval_a_exp sa4.1.(seq_regs) writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold sa4, writeSuccessWithdrawalsPrefixStatea4, sa0,
      writeSuccessWithdrawalsPrefixStatea0, writeSuccess156a0After,
      writeSuccess15694Local, writeSuccess156a0Regs,
      writeSuccess15694Mstatus in *. cbn in *.
    rewrite !lookup_insert_ne; try discriminate. exact Hmstatus. }
  destruct (segment_156a4_mstatus_covered sa4.1.(seq_regs) sa4.2
    observations4 middle4 Hpca4 Hx1_a4 Hcodea4 Hcode101d4 Hmstatusa4 Hseg4)
    as (Hmiddle4 & Hobs4).
  subst observations4.
  have Hsegments4 : segments4 = [] by (inversion Hrun4; reflexivity).
  have Hmachine : middle4 = after.1 by (inversion Hrun4; reflexivity).
  rewrite Hmiddle4 in Hmachine.
  rewrite Hmiddle4 in Hseg4.
  have HafterEq : after =
      (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer, state.2).
  { destruct after as [afterMachine afterLog]. cbn in Hmachine, Hlog |- *.
    subst afterMachine. f_equal.
    rewrite Hsegments4 in Hlog.
  unfold writeSuccess15694Observations, writeSuccess15694PrefixObservations,
    writeSuccess15698Observations, writeSuccess15698PrefixObservations,
    writeSuccess1569cObservations, writeSuccess1569cPrefixObservations,
    writeSuccess156a0Observations, writeSuccess156a0PrefixObservations,
    writeSuccess156a4Observations, writeSuccess156a4Prefix8Observations,
    writeSuccess156a4TailObservations,
    writeSuccess156a4TailFirst2Observations,
    writeSuccess156a4TailLastObservations in Hlog.
    cbn [flattenMicroObservations segmentRecords segmentRecordsFrom] in Hlog.
    rewrite app_nil_r in Hlog. exact Hlog. }
  exists (writeSuccess15694Observations state.1.1.(seq_regs) state.1.2 sp),
    (writeSuccess15698Observations s98.1.(seq_regs) s98.2),
    (writeSuccess1569cObservations s9c.1.(seq_regs) s9c.2 pointer),
    (writeSuccess156a0Observations sa0.1.(seq_regs) sa0.2),
    (writeSuccess156a4Observations sa4.1.(seq_regs) sa4.2).
  split; first (rewrite Hsegments4; reflexivity).
  split; first exact HafterEq.
  split.
  - change (WriteSuccessWithdrawalsRecordedRun 1 state
      [writeSuccess15694Observations state.1.1.(seq_regs) state.1.2 sp] (s98, state.2)).
    change (WriteSuccessWithdrawalsRecordedRun (S 0) state ([] ++ [writeSuccess15694Observations state.1.1.(seq_regs) state.1.2 sp])
      (s98, state.2)).
    eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0 state [] state).
    + apply writeSuccessWithdrawalsRecordedRunZero.
    + exact Hseg0.
    + unfold writeSuccess15694Observations,
        writeSuccess15694PrefixObservations. reflexivity.
  - split.
    + change (WriteSuccessWithdrawalsRecordedRun (S 0) (s98, state.2)
        ([] ++ [writeSuccess15698Observations s98.1.(seq_regs) s98.2]) (s9c, state.2)).
      eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0 (s98, state.2) []
        (s98, state.2)).
      * apply writeSuccessWithdrawalsRecordedRunZero.
      * exact Hseg1.
      * unfold writeSuccess15698Observations,
          writeSuccess15698PrefixObservations. reflexivity.
    + split.
      * change (WriteSuccessWithdrawalsRecordedRun (S 0) (s9c, state.2)
          ([] ++ [writeSuccess1569cObservations s9c.1.(seq_regs) s9c.2 pointer]) (sa0, state.2)).
        eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0 (s9c, state.2) []
          (s9c, state.2)).
        -- apply writeSuccessWithdrawalsRecordedRunZero.
        -- exact Hseg2.
        -- unfold writeSuccess1569cObservations,
            writeSuccess1569cPrefixObservations. reflexivity.
      * split.
        -- change (WriteSuccessWithdrawalsRecordedRun (S 0) (sa0, state.2)
            ([] ++ [writeSuccess156a0Observations sa0.1.(seq_regs) sa0.2]) (sa4, state.2)).
           eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
             (sa0, state.2) [] (sa0, state.2)).
           ++ apply writeSuccessWithdrawalsRecordedRunZero.
           ++ exact Hseg3.
           ++ unfold writeSuccess156a0Observations,
                writeSuccess156a0PrefixObservations. reflexivity.
        -- change (WriteSuccessWithdrawalsRecordedRun (S 0) (sa4, state.2)
            ([] ++ [writeSuccess156a4Observations sa4.1.(seq_regs) sa4.2])
            (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer,
             state.2)).
           eapply (writeSuccessWithdrawalsSilentRecordedSnoc 0
             (sa4, state.2) [] (sa4, state.2)).
           ++ apply writeSuccessWithdrawalsRecordedRunZero.
           ++ exact Hseg4.
           ++ unfold writeSuccess156a4Observations,
                writeSuccess156a4Prefix8Observations,
                writeSuccess156a4TailObservations,
                writeSuccess156a4TailFirst2Observations,
                writeSuccess156a4TailLastObservations. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694PositionsExact.

(* The five one-step runs expose all prefix positions. *)
