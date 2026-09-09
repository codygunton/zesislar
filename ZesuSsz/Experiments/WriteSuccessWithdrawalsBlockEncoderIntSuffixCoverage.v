From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34Coverage.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntSuffixRunCovered
    (regs : reg_map) (global : seq_global_state)
    (sp returnAddress : bv 64) segments after :
  regs !! "x2" = Some (RVal_Bits (sp - BV 64 16)%bv) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Link) ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  read_mem global.(seq_mem) (bv_unsigned sp - 8) 8%N =
    Some (bv_to_bvn returnAddress) ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 0x40000000 ->
  bv_extract 0 2 returnAddress = BV 2 0 ->
  writeSuccessWithdrawalsInstructionTable global ->
  IslaInstructionRun 3
    (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global)
    segments after ->
  exists mstatusBits satp,
    after = writeSuccess15d34After
      (writeSuccess15d30Regs
        (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
          returnAddress) (sp - BV 64 16)%bv) global returnAddress /\
    segments =
      [writeSuccess15d2cObservations
        (writeSuccessEncoderIntAfterOutputRegs regs) global mstatusBits
        (sp - BV 64 16)%bv satp returnAddress;
       writeSuccess15d30Observations
        (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
          returnAddress) global (sp - BV 64 16)%bv;
       writeSuccess15d34Observations
        (writeSuccess15d30Regs
          (writeSuccess15d2cRegs (writeSuccessEncoderIntAfterOutputRegs regs)
            returnAddress) (sp - BV 64 16)%bv) global returnAddress].
Proof.
  intros Hx2 Hx1 Hfacts Hread Hrange Halign HramLower HramUpper HreturnAlign
    Htable Hrun.
  destruct (writeSuccessEncoderIntSuffixInstructionFacts global Htable) as
    (Hcode2c & Hcode30 & Hcode34).
  destruct (writeSuccessOutputRegisterFacts regs Hfacts) as
    (mstatusBits & satp & oldX5 & HoldX5 & HmstatusRoot & Hsatp & Hsys &
     Hmstatus).
  have HoutX2 : writeSuccessEncoderIntAfterOutputRegs regs !! "x2" =
      Some (RVal_Bits (sp - BV 64 16)%bv).
  { rewrite writeSuccessEncoderIntAfterOutputLookupOther;
      [exact Hx2|congruence|congruence]. }
  have HoutPc : writeSuccessEncoderIntAfterOutputRegs regs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15d2c)).
  { unfold writeSuccessEncoderIntAfterOutputRegs, writeSuccess101a0Regs.
    rewrite lookup_insert. repeat apply f_equal. apply bv_eq.
    native_compute. reflexivity. }
  have HoutX1 : writeSuccessEncoderIntAfterOutputRegs regs !! "x1" =
      Some (RVal_Bits writeSuccess15d28Link).
  { rewrite writeSuccessEncoderIntAfterOutputLookupOther;
      [exact Hx1|congruence|congruence]. }
  have HoutMstatusRoot : writeSuccessEncoderIntAfterOutputRegs regs !! "mstatus" =
      Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]).
  { rewrite writeSuccessEncoderIntAfterOutputLookupOther;
      [exact HmstatusRoot|congruence|congruence]. }
  have HoutSatp : writeSuccessEncoderIntAfterOutputRegs regs !! "satp" =
      Some (RVal_Bits satp).
  { rewrite writeSuccessEncoderIntAfterOutputLookupOther;
      [exact Hsatp|congruence|congruence]. }
  have HoutSys := writeSuccessEncoderIntOutputSysRegs regs Hsys.
  have HoutMstatus := writeSuccessEncoderIntOutputMstatus regs Hmstatus.
  have HstackRange : islaMemoryRange (bv_unsigned (sp - BV 64 16)%bv) 16.
  { rewrite writeSuccessEncoderIntStackUnsigned; assumption. }
  have HstackAlign : bv_unsigned (sp - BV 64 16)%bv `mod` 8 = 0.
  { rewrite writeSuccessEncoderIntStackUnsigned; [|assumption]. lia. }
  have HstackLower : 0x20000000 <= bv_unsigned (sp - BV 64 16)%bv.
  { rewrite writeSuccessEncoderIntStackUnsigned; assumption. }
  have HstackUpper : bv_unsigned (sp - BV 64 16)%bv + 16 <= 0x40000000.
  { rewrite writeSuccessEncoderIntStackUnsigned; [|assumption]. lia. }
  destruct (writeSuccessEncoderIntLoadAssumes
    (writeSuccessEncoderIntAfterOutputRegs regs)
    (sp - BV 64 16)%bv HoutX2
    (proj1 (proj2 (proj2 HoutSys)))
    (proj1 (proj2 (proj2 (proj2 HoutSys)))) HstackRange HstackAlign
    HstackLower HstackUpper) as (Ha2c & Hl2c & Hu2c).
  have Haddress2c :
      bv_unsigned (writeSuccess15d2cAddress (sp - BV 64 16)%bv) =
      bv_unsigned sp - 8.
  { unfold writeSuccess15d2cAddress. apply Z.le_antisymm; bv_solve. }
  have Hread2c : read_mem global.(seq_mem)
      (bv_unsigned (writeSuccess15d2cAddress (sp - BV 64 16)%bv)) 8 =
      Some (bv_to_bvn returnAddress).
  { rewrite Haddress2c. exact Hread. }
  destruct (segment_15d2c (writeSuccessEncoderIntAfterOutputRegs regs) global
    mstatusBits (sp - BV 64 16)%bv satp returnAddress writeSuccess15d28Link
    HoutPc HoutX2 HoutMstatusRoot HoutSatp HoutX1
    HoutSys HoutMstatus Ha2c Hl2c Hu2c Hread2c Hcode2c Hcode30) as
    (Hseg2c & _).
  set (regs2c := writeSuccess15d2cRegs
    (writeSuccessEncoderIntAfterOutputRegs regs) returnAddress).
  have Hpc30 : regs2c !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d30)).
  { unfold regs2c, writeSuccess15d2cRegs. rewrite lookup_insert.
    rewrite writeSuccess15d2cNextPcExact. reflexivity. }
  have Hx2_2c : regs2c !! "x2" =
      Some (RVal_Bits (sp - BV 64 16)%bv).
  { unfold regs2c. rewrite writeSuccess15d2cRegsLookupOther;
      [exact HoutX2|congruence|congruence]. }
  have Hmstatus2c : eval_a_exp regs2c writeSuccess15d30Mstatus =
      Some (Val_Bool true).
  { unfold regs2c, writeSuccess15d30Mstatus, writeSuccess15694Mstatus
      in HoutMstatus |- *.
    cbn in HoutMstatus |- *. rewrite writeSuccess15d2cRegsLookupOther;
      [exact HoutMstatus|congruence|congruence]. }
  destruct (segment_15d30_mstatus regs2c global (sp - BV 64 16)%bv
    (RVal_Bits (sp - BV 64 16)%bv) Hpc30 Hx2_2c Hx2_2c Hcode30 Hcode34
    Hmstatus2c) as (Hseg30 & _).
  set (regs30 := writeSuccess15d30Regs regs2c (sp - BV 64 16)%bv).
  have Hpc34 : regs30 !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d34)).
  { unfold regs30, writeSuccess15d30Regs. rewrite lookup_insert.
    reflexivity. }
  have Hx1_30 : regs30 !! "x1" = Some (RVal_Bits returnAddress).
  { unfold regs30. rewrite writeSuccess15d30RegsLookupOther;
      [|congruence|congruence].
    unfold regs2c, writeSuccess15d2cRegs.
    rewrite lookup_insert_ne; [|congruence]. rewrite lookup_insert. reflexivity. }
  have Hmstatus30 : eval_a_exp regs30 writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold regs30, writeSuccess15694Mstatus in Hmstatus2c |- *.
    unfold writeSuccess15d30Mstatus in Hmstatus2c.
    cbn in Hmstatus2c |- *. rewrite writeSuccess15d30RegsLookupOther;
      [exact Hmstatus2c|congruence|congruence]. }
  have Halign34 : eval_a_exp regs30 writeSuccess15d34Alignment =
      Some (Val_Bool true).
  { change (eval_a_exp regs30 writeSuccess101a0Alignment =
      Some (Val_Bool true)).
    apply (writeSuccessOutputReturnAlignmentEval regs30 returnAddress);
      assumption. }
  destruct (segment_15d34 regs30 global returnAddress Hpc34 Hx1_30 Hcode34
    Hmstatus30 Halign34) as (Hseg34 & Hmemory34).
  inversion Hrun as [|? ? obs2c after2c ? ? Hactual2c Htail1]; subst.
  inversion Htail1 as [|? ? obs30 after30 ? ? Hactual30 Htail2]; subst.
  inversion Htail2 as [|? ? obs34 after34 ? ? Hactual34 Hzero]; subst.
  inversion Hzero; subst.
  destruct (segment_15d2c_covered (writeSuccessEncoderIntAfterOutputRegs regs)
    global mstatusBits (sp - BV 64 16)%bv satp returnAddress
    writeSuccess15d28Link obs2c after2c HoutPc HoutX2 HoutMstatusRoot HoutSatp
    HoutX1 HoutSys HoutMstatus Ha2c Hl2c Hu2c Hread2c Hcode2c Hcode30
    Hactual2c) as (Hafter2c & Hobs2c). subst after2c.
  destruct (segment_15d30_covered regs2c global (sp - BV 64 16)%bv
    (RVal_Bits (sp - BV 64 16)%bv) obs30 after30 Hpc30 Hx2_2c Hx2_2c
    Hcode30 Hcode34 Hmstatus2c Hactual30) as (Hafter30 & Hobs30).
  subst after30.
  destruct (segment_15d34_covered regs30 global returnAddress obs34 after
    Hpc34 Hx1_30 Hcode34 Hmstatus30 Halign34 Hactual34) as
    (Hafter34 & Hobs34).
  exists mstatusBits, satp. split; first exact Hafter34.
  unfold regs2c, regs30 in *.
  rewrite Hobs2c Hobs30 Hobs34. reflexivity.
Qed.

Print Assumptions writeSuccessEncoderIntSuffixRunCovered.
