From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputPositionContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputPositionState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInvContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPositionEdges.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Import ListNotations.
Open Scope Z_scope.

Theorem writeSuccessWithdrawalsOutputActualPositionStates args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal segments after :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
    writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).2
      (sp + BV 64 1768)%bv = writeSuccess10190Before outputRegs outputGlobal ->
  WriteSuccessWithdrawalsRecordedRun 5
    (writeSuccess10190Before outputRegs outputGlobal,
     writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
       withdrawal) segments after ->
  exists states,
    length states = 6%nat /\
    nth_error states 0 = Some
      (writeSuccess10190Before outputRegs outputGlobal,
       writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
         withdrawal) /\
    nth_error states 5 = Some after /\
    WriteSuccessWithdrawalsPositionEdges segments states /\
    forall offset stateAt,
      (offset < 5)%nat ->
      nth_error states offset = Some stateAt ->
      writeSuccessWithdrawalsPositionState remaining (384 + offset) stateAt.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2 Houtput Hrun.
  have HoutputInv := writeSuccessWithdrawals156c0OutputInv args sp pointer base
    total processed (S remaining) withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  rewrite Houtput in HoutputInv.
  unfold Inv_write_output in HoutputInv. cbn in HoutputInv.
  destruct HoutputInv as
    (Hboundary & HpcReg & Hconcrete & Hx1 & Hx10 & Hx11 & Halign & Hreturn &
     Hsize & Hread & Htable & Hfacts & Hmmio & Hlog).
  destruct Hreturn as (returnTrace & Hreturn).
  destruct Hboundary as (Hnb & pc & trace & Hpc & Hsource & Htrace).
  cbn in HpcReg, Hpc, Hconcrete.
  change (match outputRegs !! "PC" with
    | Some (RVal_Bits value) => Some (bvn_unsigned value)
    | _ => None
    end = Some 0x10190) in Hconcrete.
  rewrite Hpc in Hconcrete. inversion Hconcrete as [Hunsigned].
  change (bv_unsigned pc = 0x10190) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x10190.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc), Hunsigned. reflexivity. }
  subst pc.
  destruct (writeSuccessWithdrawalsOutputPositionContext args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal Hinv Hprefix Hentry1 Hentry2
    Houtput) as (_ & Hx9 & Hrange).
  eapply writeSuccessOutputRecordedPositionStates; eassumption.
Qed.

Print Assumptions writeSuccessWithdrawalsOutputActualPositionStates.
