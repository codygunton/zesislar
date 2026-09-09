From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsFinalAmountRead.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156dcLoopTailRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputContextFromInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration410Context.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationThroughFinalEncoder.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156c0OutputInv.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.

Definition writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
    withdrawal :=
  writeSuccessWithdrawalsEncoderIntEndpoint finalRegs finalGlobal sp
    (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal).

Definition writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
    pointer remaining withdrawal :=
  writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining))
    (writeSuccess156e0Regs
      (writeSuccess156dcRegs
        (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
          withdrawal).1.(seq_regs) pointer)
      (Z_to_bv 64 (Z.of_nat (S remaining))))
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).2.

Definition writeSuccessWithdrawalsIteration410Log priorLog global1 global2
    outputGlobal finalGlobal sp withdrawal :=
  (writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp
      withdrawal ++
    writeSuccessWithdrawalsOutputRecordsExact outputGlobal
      (sp + BV 64 1768)%bv (BV 64 20)) ++
  writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp
    (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal).

Lemma writeSuccessWithdrawalsIteration410 args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed (S remaining) withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  exists segments regs0 global0 regs1 global1 regs2 global2 outputRegs
      outputGlobal finalRegs finalGlobal,
    WriteSuccessWithdrawalsRecordedRun 410 state segments
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
         pointer remaining withdrawal,
       writeSuccessWithdrawalsIteration410Log priorLog global1 global2
         outputGlobal finalGlobal sp withdrawal) /\
    writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
      writeSuccess101d4Before regs0 global0 /\
    writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer
      current withdrawal = writeSuccess15d10Before regs1 global1 /\
    writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal =
      writeSuccess15d10Before regs2 global2 /\
    writeSuccessWithdrawalsOutputEntry
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp
        withdrawal).2 (sp + BV 64 1768)%bv =
      writeSuccess10190Before outputRegs outputGlobal /\
    writeSuccess156d8After
      (writeSuccess156d4Regs
        (writeSuccess156d0Regs
          (writeSuccessOutputEndpointRegs outputRegs (Z_to_bv 64 0x156d0))
          (writeSuccessWithdrawalsAmountValue withdrawal))) outputGlobal =
      writeSuccess15d10Before finalRegs finalGlobal /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalIndex withdrawal))
      (writeSuccessWithdrawalsEncoderIntRecords global1 sp
        (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalValidatorIndex withdrawal))
      (writeSuccessWithdrawalsEncoderIntRecords global2 sp
        (Z_to_bv 64 0x156c0)
        (writeSuccessWithdrawalsValidatorValue withdrawal)) /\
    writeSuccessOutputRecords (sp + BV 64 1768)%bv (BV 64 20)
      (writeSuccessWithdrawalAddressBytes withdrawal)
      (writeSuccessWithdrawalsOutputRecordsExact outputGlobal
        (sp + BV 64 1768)%bv (BV 64 20)) /\
    writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessWithdrawalIntegerBytes
        (observationWithdrawalAmount withdrawal))
      (writeSuccessWithdrawalsEncoderIntRecords finalGlobal sp
        (Z_to_bv 64 0x156dc) (writeSuccessWithdrawalsAmountValue withdrawal)).
Proof.
  intros Hinv.
  destruct (writeSuccessWithdrawalsIterationThroughFinalEncoder args sp
    pointer base total processed (S remaining) withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog
    state Hinv) as
    (first & regs0 & global0 & regs1 & global1 & regs2 & global2 & outputRegs &
     outputGlobal & finalRegs & finalGlobal & Hfirst & Hp & He1 & He2 & Ho &
     HfinalEntry & Hindex & Hvalidator & Haddress & Hamount).
  destruct (writeSuccessWithdrawals407EndpointTailFacts args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 regs2 global2 outputRegs outputGlobal finalRegs finalGlobal Hinv Hp
    He1 He2 Ho HfinalEntry) as
    (Hendpoint & Hpc & Hx8 & Hx9 & Hmstatus & Htable).
  destruct (writeSuccessWithdrawals156dcLoopTailRecordedDirect
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsIteration410Endpoint finalRegs finalGlobal sp
      withdrawal).2 pointer remaining
    (writeSuccessWithdrawalsIteration410Log priorLog global1 global2
      outputGlobal finalGlobal sp withdrawal)
    Hpc Hx8 Hx9 Hmstatus Htable) as (tail & Htail).
  unfold writeSuccessWithdrawalsIteration410Endpoint in Htail.
  rewrite <- Hendpoint in Htail.
  have Hrun : WriteSuccessWithdrawalsRecordedRun 410 state (first ++ tail)
      (writeSuccessWithdrawalsIteration410Machine finalRegs finalGlobal sp
         pointer remaining withdrawal,
       writeSuccessWithdrawalsIteration410Log priorLog global1 global2
         outputGlobal finalGlobal sp withdrawal).
  { replace 410%nat with (407 + 3)%nat by reflexivity.
    unfold writeSuccessWithdrawalsIteration410Machine in Htail |- *.
    eapply writeSuccessWithdrawalsRecordedRunApp.
    - exact Hfirst.
    - exact Htail. }
  exists (first ++ tail), regs0, global0, regs1, global1, regs2, global2,
    outputRegs, outputGlobal, finalRegs, finalGlobal.
  split; first exact Hrun.
  split; first exact Hp.
  split; first exact He1.
  split; first exact He2.
  split; first exact Ho.
  split; first exact HfinalEntry.
  split; first exact Hindex.
  split; first exact Hvalidator.
  split; first exact Haddress.
  exact Hamount.
Qed.

Print Assumptions writeSuccessWithdrawalsIteration410.

