From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1568c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1568cCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlock1568c.

Import ListNotations.
Open Scope Z_scope.

Definition block_1568c_guard_coverage_statement : Prop :=
  forall args sp base total allBytes scratch encoderScratch registerFrame
      memoryFrame priorLog state segments machineAfter,
    Inv_1568c args sp base total allBytes scratch encoderScratch registerFrame
      memoryFrame priorLog state ->
    IslaInstructionRun 2 state.1 segments machineAfter ->
    match total with
    | O =>
        Inv_156e8 args sp (Z_to_bv 64 base) base 0 allBytes registerFrame
          memoryFrame priorLog (machineAfter, priorLog)
    | S remaining =>
        exists withdrawal current suffix,
          nth_error (observationWithdrawals
            (successDecoded WriteSuccessObservation args)) 0 =
            Some withdrawal /\
          allBytes = current ++ suffix /\
          length current = 48%nat /\
          Inv_15694 args sp (Z_to_bv 64 base) base total 0 (S remaining)
            withdrawal allBytes [] current suffix scratch encoderScratch
            registerFrame memoryFrame priorLog (machineAfter, priorLog)
    end.

Lemma block_1568c_run_covered args sp base total allBytes scratch encoderScratch
    registerFrame memoryFrame priorLog state segments machineAfter :
  Inv_1568c args sp base total allBytes scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  IslaInstructionRun 2 state.1 segments machineAfter ->
  exists regs global,
    state.1 = writeSuccess1568cBefore regs global /\
    segments =
      [writeSuccess1568cObservations regs global sp;
       writeSuccess15690Observations (Z_to_bv 64 (Z.of_nat total))
         (writeSuccess1568cRegs regs sp) global] /\
    machineAfter = writeSuccess15690After
      (Z_to_bv 64 (Z.of_nat total)) (writeSuccess1568cRegs regs sp) global.
Proof.
  intros Hinv Hrun.
  destruct state as [[[trace regs pcRegister nb] global] log].
  cbn in Hinv, Hrun |- *.
  have Hboundary : IslaInstructionBoundary
      ({| seq_trace := trace; seq_regs := regs; seq_pc_reg := pcRegister;
          seq_nb_state := nb |}, global) by
    (unfold Inv_1568c in Hinv; tauto).
  have HpcRegister : pcRegister = "PC" by
    (unfold Inv_1568c in Hinv; tauto).
  subst pcRegister.
  have HconcretePc :
      match regs !! "PC" with
      | Some (RVal_Bits value) => Some (bvn_unsigned value)
      | _ => None
      end = Some 0x1568c by
    (unfold Inv_1568c, writeSuccessWithdrawalsConcretePc in Hinv;
      cbn in Hinv; tauto).
  destruct Hboundary as (Hnb & pc & source & Hpc & Hsource & Htrace).
  cbn in Hpc, Hsource, Htrace.
  rewrite Hpc in HconcretePc. inversion HconcretePc as [Hunsigned].
  change (bv_unsigned pc = 0x1568c) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x1568c.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc), Hunsigned. reflexivity. }
  subst pc.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_1568c in Hinv; tauto).
  have Hcode1568c : global.(seq_instrs) !! Z_to_bv 64 0x1568c =
      Some IslaTraces.write_success_89.a1568c.a1568c.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  rewrite Hcode1568c in Hsource. inversion Hsource. subst source.
  subst trace. destruct nb; first discriminate Hnb. clear Hnb.
  have Hsp : regs !! "x2" = Some (RVal_Bits sp) by
    (unfold Inv_1568c in Hinv; tauto).
  have Hx9 : regs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat total))) by
    (unfold Inv_1568c in Hinv; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts regs by
    (unfold Inv_1568c in Hinv; tauto).
  have Hmstatus : eval_a_exp regs writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold writeSuccessWithdrawalsOperationalRegisterFacts in Hfacts.
    unfold writeSuccessWithdrawalsOperationalMstatus in Hfacts.
    exact (proj1 Hfacts). }
  have Hcode15690 : global.(seq_instrs) !! Z_to_bv 64 0x15690 =
      Some IslaTraces.write_success_89.a15690.a15690.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode15694 : global.(seq_instrs) !! Z_to_bv 64 0x15694 =
      Some IslaTraces.write_success_90.a15694.a15694.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode156e8 : global.(seq_instrs) !! Z_to_bv 64 0x156e8 =
      Some IslaTraces.write_success_96.a156e8.a156e8.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hx18Owned : exists oldX18, regs !! "x18" = Some oldX18 by
    (unfold Inv_1568c in Hinv; tauto).
  destruct Hx18Owned as (x18 & Hx18).
  set (middleRegs := writeSuccess1568cRegs regs sp).
  have HmiddlePc : middleRegs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15690)).
  { unfold middleRegs, writeSuccess1568cRegs. rewrite lookup_insert.
    rewrite writeSuccess1568cNextPcExact. reflexivity. }
  have HmiddleX9 : middleRegs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat total))).
  { unfold middleRegs. rewrite writeSuccess1568cRegsLookupOther; congruence. }
  have HmiddleMstatus : eval_a_exp middleRegs writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold middleRegs, writeSuccess15694Mstatus in Hmstatus |- *.
    cbn in Hmstatus |- *. rewrite writeSuccess1568cRegsLookupOther;
      try discriminate. exact Hmstatus. }
  inversion Hrun as [|firstCount before first middle rest final Hfirst Hrest];
    subst.
  inversion Hrest as [|secondCount before' second middle' rest' final'
    Hsecond Hzero]; subst.
  inversion Hzero; subst.
  destruct (segment_1568c_covered regs global sp x18 first middle
    Hpc Hsp Hx18 Hcode1568c Hcode15690 Hmstatus Hfirst) as
    (Hmiddle & HfirstObs).
  subst middle.
  destruct (segment_15690_covered middleRegs global
    (Z_to_bv 64 (Z.of_nat total)) second machineAfter HmiddlePc HmiddleX9
    Hcode15690 Hcode15694 Hcode156e8 HmiddleMstatus Hsecond) as
    (Hafter & HsecondObs).
  subst middleRegs. exists regs, global. split; first reflexivity. split.
  - rewrite HfirstObs HsecondObs. reflexivity.
  - exact Hafter.
Qed.

Lemma block_1568c_covered : block_1568c_guard_coverage_statement.
Proof.
  unfold block_1568c_guard_coverage_statement.
  intros args sp base total allBytes scratch encoderScratch registerFrame
    memoryFrame priorLog state segments machineAfter Hinv Hrun.
  pose proof block_1568c as Hexists.
  unfold block_1568c_guard_statement in Hexists.
  destruct (Hexists args sp base total allBytes scratch encoderScratch
    registerFrame memoryFrame priorLog state Hinv) as
    (expectedSegments & expectedAfter & HexpectedRun & HexpectedLog & Hpost).
  pose proof (block_1568c_run_covered args sp base total allBytes scratch
    encoderScratch registerFrame memoryFrame priorLog state segments machineAfter
    Hinv Hrun) as (regs & global & HactualBefore & _ & HactualAfter).
  pose proof (block_1568c_run_covered args sp base total allBytes scratch
    encoderScratch registerFrame memoryFrame priorLog state expectedSegments
    expectedAfter.1 Hinv HexpectedRun) as
    (expectedRegs & expectedGlobal & HexpectedBefore & _ & HexpectedAfter).
  have Hmachine : machineAfter = expectedAfter.1.
  { have Hbefore : writeSuccess1568cBefore regs global =
        writeSuccess1568cBefore expectedRegs expectedGlobal by congruence.
    unfold writeSuccess1568cBefore, writeSuccess1568cLocal in Hbefore.
    inversion Hbefore. subst expectedRegs expectedGlobal.
    by rewrite HactualAfter HexpectedAfter. }
  destruct expectedAfter as [expectedMachine expectedLog]. cbn in *.
  subst expectedMachine expectedLog. rewrite Hmachine. exact Hpost.
Qed.

Print Assumptions block_1568c_run_covered.
Print Assumptions block_1568c_covered.
