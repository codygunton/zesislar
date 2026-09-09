From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputRun.
Import ListNotations.
Open Scope Z_scope.

Lemma block_write_output : block_write_output_statement.
Proof.
  unfold block_write_output_statement.
  intros data size returnAddress bytes priorLog state Hinv.
  destruct state as [[local global] log].
  destruct local as [trace regs pcRegister nb]. cbn in Hinv |- *.
  destruct Hinv as
    (Hboundary & HpcRegister & HconcretePc & Hx1 & Hx10 & Hx11 &
     HreturnAlign & HreturnCode & Hsize & Hread & Htable & HregisterFacts &
     HmemoryDom & Hlog).
  cbn in HpcRegister, Hlog, HreturnCode, Htable, HregisterFacts,
    HmemoryDom, Hx1, Hx10, Hx11, Hread, HconcretePc.
  subst pcRegister log.
  destruct HreturnCode as (returnTrace & HreturnLookup).
  destruct Hboundary as (Hnb & pc & source & Hpc & Hsource & Htrace).
  cbn in Hnb, Hpc, Hsource, Htrace, HconcretePc.
  subst nb trace.
  change (match regs !! "PC" with
    | Some (RVal_Bits value) => Some (bvn_unsigned value)
    | _ => None
    end = Some 0x10190) in HconcretePc.
  rewrite Hpc in HconcretePc. inversion HconcretePc as [Hunsigned].
  change (bv_unsigned pc = 0x10190) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x10190.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc). rewrite Hunsigned. reflexivity. }
  subst pc.
  have Hcode90 := proj1 (writeSuccessOutputInstructionFacts global Htable).
  rewrite Hsource in Hcode90. inversion Hcode90. subst source.
  destruct (writeSuccessOutputRecordedComposition regs global data size
    returnAddress bytes priorLog returnTrace Hpc Hx1 Hx10 Hx11
    HreturnAlign HreturnLookup Hsize Hread Htable HregisterFacts HmemoryDom) as
    (segments & finalMachine & records & Hrecorded & HfinalPc & Hrecords).
  destruct Hrecorded as (Hrun & HfinalLog).
  exists segments, (finalMachine, priorLog ++ records), records.
  split; first exact Hrun. split; first exact HfinalPc.
  split; [reflexivity | exact Hrecords].
Qed.

Print Assumptions block_write_output.
