From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntCoverageComposition.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsEncoderIntEndpoint regs global sp
    returnAddress value : IslaState :=
  writeSuccess15d34After
    (writeSuccess15d30Regs
      (writeSuccess15d2cRegs
        (writeSuccessEncoderIntAfterOutputRegs
          (writeSuccessEncoderIntRegs7 regs sp)) returnAddress)
      (sp - BV 64 16)%bv)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    returnAddress.

Definition writeSuccessWithdrawalsEncoderIntRecords global sp returnAddress
    value : list WriteSuccessRecord :=
  [(SWriteMem (BV 64 0x2401a0c0)
      (bv_to_bvn (sp - BV 64 16)%bv),
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem));
   (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn (BV 64 8)),
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem))].

Lemma block_encoder_int_recorded_covered_exact value sp returnAddress scratch
    memoryFrame priorLog state segments after :
  Inv_encoder_int value sp returnAddress scratch memoryFrame priorLog state ->
  WriteSuccessWithdrawalsRecordedRun 15 state segments after ->
  exists regs global,
    state.1 = writeSuccess15d10Before regs global /\
    after =
      (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp returnAddress
         value,
       priorLog ++ writeSuccessWithdrawalsEncoderIntRecords global sp
         returnAddress value).
Proof.
  intros Hinv (Hrun & HafterLog).
  destruct state as [[local global] log].
  destruct local as [trace regs pcRegister nb].
  cbn in Hinv, Hrun, HafterLog |- *.
  destruct Hinv as
    (Hboundary & HpcRegister & HconcretePc & Hx1 & Hx2 & Hx10 &
     HreturnAlign & HreturnLookup & HstackAlign & HramLower & HramUpper &
     Hread & Hrange & Hbacked & Hframe & Htable & Hfacts & Hmmio & Hlog).
  destruct HreturnLookup as (returnTrace & HreturnTrace).
  cbn in HpcRegister, Hlog, Htable, Hfacts, Hmmio, Hx1, Hx2, Hx10,
    Hread, HconcretePc, Hframe, Hbacked, HreturnTrace.
  subst pcRegister log.
  destruct Hboundary as (Hnb & pc & source & Hpc & Hsource & Htrace).
  cbn in Hnb, Hpc, Hsource, Htrace, HconcretePc. subst nb trace.
  change (match regs !! "PC" with
    | Some (RVal_Bits value) => Some (bvn_unsigned value)
    | _ => None
    end = Some 0x15d10) in HconcretePc.
  rewrite Hpc in HconcretePc. inversion HconcretePc as [Hunsigned].
  change (bv_unsigned pc = 0x15d10) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x15d10.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc), Hunsigned. reflexivity. }
  subst pc.
  have Hcode10 := proj1 (writeSuccessEncoderIntInstructionFacts global Htable).
  rewrite Hsource in Hcode10. inversion Hcode10. subst source.
  destruct (writeSuccessEncoderIntRunExact regs global value sp returnAddress
    scratch memoryFrame returnTrace segments after.1 Hpc Hx1 Hx2 Hx10
    HreturnAlign HreturnTrace HstackAlign HramLower HramUpper Hread Hrange
    Hbacked Hframe Htable Hfacts Hmmio Hrun) as (Hafter & Hrecords).
  exists regs, global. split; first reflexivity.
  destruct after as [afterMachine afterLog]. cbn in Hafter, HafterLog |- *.
  subst afterMachine.
  unfold writeSuccessWithdrawalsEncoderIntEndpoint.
  unfold writeSuccessWithdrawalsEncoderIntRecords.
  rewrite Hrecords in HafterLog. subst afterLog. reflexivity.
Qed.

Print Assumptions block_encoder_int_recorded_covered_exact.
