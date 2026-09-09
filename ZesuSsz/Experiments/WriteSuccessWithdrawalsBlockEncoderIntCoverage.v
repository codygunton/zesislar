From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntFrame.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntCoverageComposition.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.

Import ListNotations.
Open Scope Z_scope.

Definition block_encoder_int_coverage_statement : Prop :=
  forall value sp returnAddress scratch memoryFrame priorLog state segments after,
    Inv_encoder_int value sp returnAddress scratch memoryFrame priorLog state ->
    WriteSuccessWithdrawalsRecordedRun 15 state segments after ->
    exists records,
      writeSuccessWithdrawalsConcretePc after = Some (bv_unsigned returnAddress) /\
      read_mem_list after.1.2.(seq_mem) (bv_unsigned sp - 16) 8%N =
        Some (bv_to_little_endian 8 8 (bv_unsigned value)) /\
      writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
        after.1.2.(seq_mem) memoryFrame /\
      after.2 = priorLog ++ records /\
      writeSuccessOutputRecords (sp - BV 64 16)%bv (BV 64 8)
        (bv_to_little_endian 8 8 (bv_unsigned value)) records.

Lemma block_encoder_int_covered : block_encoder_int_coverage_statement.
Proof.
  unfold block_encoder_int_coverage_statement.
  intros value sp returnAddress scratch memoryFrame priorLog state segments after
    Hinv Hrecorded.
  destruct Hrecorded as (Hrun & HafterLog).
  destruct state as [[local global] log].
  destruct local as [trace regs pcRegister nb]. cbn in Hinv, Hrun, HafterLog |- *.
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
    Hbacked Hframe Htable Hfacts Hmmio Hrun) as (Hafter & HsegmentRecords).
  set (global2 := writeSuccessEncoderIntGlobal2 global sp returnAddress value).
  set (records :=
    [(SWriteMem (BV 64 0x2401a0c0) (bv_to_bvn (sp - BV 64 16)%bv),
        global2.(seq_mem));
     (SWriteMem (BV 64 0x2401a0c8) (bv_to_bvn (BV 64 8)),
        global2.(seq_mem))]).
  have HreturnTrace2 : global2.(seq_instrs) !! returnAddress = Some returnTrace.
  { unfold global2, writeSuccessEncoderIntGlobal2,
      writeSuccessEncoderIntGlobal1, writeSuccess15d18Global,
      writeSuccess15d14Global. cbn. exact HreturnTrace. }
  have Htarget := writeSuccessEncoderInt15d34TargetExact returnAddress HreturnAlign.
  have HfinalMemory : after.1.2.(seq_mem) = global2.(seq_mem).
  { rewrite Hafter. unfold writeSuccess15d34After.
    rewrite Htarget HreturnTrace2. reflexivity. }
  have Hframe2 : writeSuccessMemoryRangeFrame (bv_unsigned sp - 16) 16
      global2.(seq_mem) memoryFrame.
  { unfold global2. apply writeSuccessEncoderIntGlobal2Frame; assumption. }
  have HdataRead : read_mem_list global2.(seq_mem)
      (bv_unsigned (sp - BV 64 16)%bv) 8%N =
      Some (bv_to_little_endian 8 8 (bv_unsigned value)).
  { rewrite writeSuccessEncoderIntStackUnsigned; [|exact Hrange].
    unfold global2. apply writeSuccessEncoderIntAfterStoresValue. exact Hrange. }
  exists records. split.
  - unfold writeSuccessWithdrawalsConcretePc. cbn. rewrite Hafter.
    unfold writeSuccess15d34After. cbn. rewrite Htarget HreturnTrace2. cbn.
    unfold writeSuccess15d34Regs. rewrite lookup_insert Htarget. reflexivity.
  - split.
    + rewrite HfinalMemory. unfold global2.
      apply writeSuccessEncoderIntAfterStoresValue. exact Hrange.
    + split.
      * rewrite HfinalMemory. exact Hframe2.
      * split.
        -- unfold records. rewrite HafterLog HsegmentRecords. reflexivity.
        -- unfold records, writeSuccessOutputRecords. split.
           ++ unfold WriteSuccessOutputSemantic.writeOutputDescriptorEvents.
              reflexivity.
           ++ cbn. rewrite bool_decide_true; last (split; bv_solve).
              unfold bvn_unsigned.
              have Hsize : bv_unsigned
                  (bvn_val (bv_to_bvn (BV 64 8))) =
                  Z.of_nat (length
                    (bv_to_little_endian 8 8 (bv_unsigned value))).
              { cbn. rewrite length_bv_to_little_endian;
                  [native_compute; reflexivity|lia]. }
              rewrite Hsize. cbn.
              replace (Z.to_N (Z.of_nat
                (length (bv_to_little_endian 8 8 (bv_unsigned value)))))
                with 8%N by (rewrite length_bv_to_little_endian; lia).
              rewrite HdataRead. reflexivity.
Qed.

Print Assumptions block_encoder_int_covered.
