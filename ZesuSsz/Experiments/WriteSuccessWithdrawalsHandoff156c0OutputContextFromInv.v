From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156c0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationOutputData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Definition writeSuccessWithdrawalsSecondEncoderLog priorLog global1 global2 sp withdrawal :=
  (priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global1 sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)) ++
  writeSuccessWithdrawalsEncoderIntRecords global2 sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal).

Definition writeSuccessWithdrawalsSecondEncoderEndpoint regs global sp withdrawal :=
  writeSuccessWithdrawalsEncoderIntEndpoint regs global sp
    (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal).

Lemma writeSuccessWithdrawalsSecondEncoderEndpointDirectFacts args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  exists oldX11 oldX10 oldX1,
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c0)) /\
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "x11" = Some oldX11 /\
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "x18" = Some (RVal_Bits (sp + BV 64 1768)%bv) /\
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "x10" = Some oldX10 /\
    (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) !! "x1" = Some oldX1 /\
    eval_a_exp (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) writeSuccess15694Mstatus = Some (Val_Bool true) /\
    writeSuccessWithdrawalsInstructionTable (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  have Hfacts2 : writeSuccessWithdrawalsOperationalRegisterFacts regs2 by (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Halign & returnTrace & Hcode).
  have HendFacts := writeSuccessEncoderIntEndpointFacts regs2 sp (Z_to_bv 64 0x156c0) Hfacts2.
  have Hpc := writeSuccessWithdrawalsEncoderIntEndpointPc regs2 global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) returnTrace Halign Hcode.
  have Hx18 := writeSuccessWithdrawalsSecondEncoderEndpointX18 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 Hinv Hprefix Hentry1 Hentry2.
  destruct (proj2 (proj2 HendFacts) "x11" ltac:(cbn; tauto)) as (x11 & Hx11).
  destruct (proj2 (proj2 HendFacts) "x10" ltac:(cbn; tauto)) as (x10 & Hx10).
  destruct (proj2 (proj2 HendFacts) "x1" ltac:(cbn; tauto)) as (x1 & Hx1).
  have Hglobal := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs2 global2 sp (Z_to_bv 64 0x156c0) (writeSuccessWithdrawalsValidatorValue withdrawal) returnTrace Halign Hcode.
  have HendExact := writeSuccessEncoderIntEndpointExact regs2 global2 sp
    (writeSuccessWithdrawalsValidatorValue withdrawal) (Z_to_bv 64 0x156c0)
    returnTrace Halign
    ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs; exact Hcode).
  have HregsEq :
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs) =
      writeSuccessEncoderIntEndpointRegs regs2 sp (Z_to_bv 64 0x156c0).
  { unfold writeSuccessWithdrawalsSecondEncoderEndpoint,
      writeSuccessWithdrawalsEncoderIntEndpoint.
    exact (f_equal (fun machine => machine.1.(seq_regs)) HendExact). }
  exists (RVal_Bits x11), (RVal_Bits x10), (RVal_Bits x1).
  rewrite HregsEq in Hpc, Hx18 |- *.
  unfold writeSuccessWithdrawalsSecondEncoderEndpoint in Hglobal |- *.
  repeat split; try assumption.
  - exact (proj1 HendFacts).
  - rewrite Hglobal. unfold writeSuccessWithdrawalsInstructionTable in Htable2 |- *. intros pc trace Hin. apply Htable2. exact Hin.
Qed.

Lemma writeSuccessWithdrawalsSecondEncoderEndpointBefore args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1 global1 regs2 global2 :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current withdrawal = writeSuccess15d10Before regs1 global1 ->
  writeSuccessWithdrawalsSecondEncoderEntry regs1 global1 sp withdrawal = writeSuccess15d10Before regs2 global2 ->
  writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal =
    writeSuccess156c0Before
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).1.(seq_regs)
      (writeSuccessWithdrawalsSecondEncoderEndpoint regs2 global2 sp withdrawal).2.
Proof.
  intros Hinv Hprefix Hentry1 Hentry2.
  have Hinv2 := writeSuccessWithdrawals156b4SecondEncoderInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs1
    global1 Hinv Hprefix Hentry1.
  rewrite Hentry2 in Hinv2.
  have Htable2 : writeSuccessWithdrawalsInstructionTable global2 by
    (unfold Inv_encoder_int in Hinv2; cbn in Hinv2; tauto).
  destruct (writeSuccessEncoderIntCaller156c0 global2 Htable2) as (Halign & trace & Hcode).
  have Hexact := writeSuccessEncoderIntEndpointExact regs2 global2 sp
    (writeSuccessWithdrawalsValidatorValue withdrawal) (Z_to_bv 64 0x156c0)
    trace Halign ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs; exact Hcode).
  have Hc0 : global2.(seq_instrs) !! Z_to_bv 64 0x156c0 = Some a156c0 by
    (apply Htable2; cbn; tauto).
  have Htrace : trace = a156c0 by congruence. subst trace.
  unfold writeSuccessWithdrawalsSecondEncoderEndpoint,
    writeSuccessWithdrawalsEncoderIntEndpoint.
  rewrite Hexact. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsSecondEncoderEndpointDirectFacts.
Print Assumptions writeSuccessWithdrawalsSecondEncoderEndpointBefore.
