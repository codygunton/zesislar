From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntComposition.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.

Import ListNotations.
Open Scope Z_scope.

Lemma block_encoder_int : block_encoder_int_statement.
Proof.
  unfold block_encoder_int_statement.
  intros value sp returnAddress scratch memoryFrame priorLog state Hinv.
  destruct state as [[local global] log].
  destruct local as [trace regs pcRegister nb]. cbn in Hinv |- *.
  destruct Hinv as
    (Hboundary & HpcRegister & HconcretePc & Hx1 & Hx2 & Hx10 &
     HreturnAlign & HstackAlign & HramLower & HramUpper & Hread & Hrange &
     Hbacked & Hframe & Htable & Hfacts & Hmmio & Hlog).
  cbn in HpcRegister, Hlog, Htable, Hfacts, Hmmio, Hx1, Hx2, Hx10,
    Hread, HconcretePc, Hframe, Hbacked.
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
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc). rewrite Hunsigned. reflexivity. }
  subst pc.
  have Hcode10 := proj1 (writeSuccessEncoderIntInstructionFacts global Htable).
  rewrite Hsource in Hcode10. inversion Hcode10. subst source.
  destruct (writeSuccessEncoderIntComposedRun regs global value sp returnAddress
    scratch memoryFrame priorLog Hpc Hx1 Hx2 Hx10 HreturnAlign HstackAlign
    HramLower HramUpper Hread Hrange Hbacked Hframe Htable Hfacts Hmmio) as
    (segments & afterMachine & records & Hrun & HfinalPc & HfinalRead &
     HfinalFrame & Hrecords).
  exists segments, (afterMachine, priorLog ++ records), records.
  split; first exact Hrun. split; first exact HfinalPc.
  split; first exact HfinalRead. split; first exact HfinalFrame.
  split; [reflexivity|exact Hrecords].
Qed.

Print Assumptions block_encoder_int.
