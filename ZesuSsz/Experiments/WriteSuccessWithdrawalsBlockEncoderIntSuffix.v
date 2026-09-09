From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d2c.
Require Import IslaTraces.write_success_07.a15d30.
Require Import IslaTraces.write_success_07.a15d34.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessEncoderIntAfterOutputRegs regs :=
  writeSuccess101a0Regs (writeSuccessOutputRegs4 regs) writeSuccess15d28Link.

Lemma writeSuccessEncoderIntAfterOutputLookupOther regs register :
  register <> "PC" -> register <> "x5" ->
  writeSuccessEncoderIntAfterOutputRegs regs !! register = regs !! register.
Proof.
  intros Hpc Hx5. unfold writeSuccessEncoderIntAfterOutputRegs.
  rewrite writeSuccess101a0RegsLookupOther; [|exact Hpc].
  apply writeSuccessOutputRegs4LookupOther; assumption.
Qed.

Lemma writeSuccessEncoderIntSuffixInstructionFacts global :
  writeSuccessWithdrawalsInstructionTable global ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d34 = Some a15d34.
Proof.
  intros Htable. repeat split; apply Htable;
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap; cbn; tauto.
Qed.

Lemma writeSuccessEncoderIntOutputSysRegs regs :
  writeSuccess10198SysRegs regs ->
  writeSuccess15d2cSysRegs (writeSuccessEncoderIntAfterOutputRegs regs).
Proof.
  unfold writeSuccess10198SysRegs, writeSuccess15d2cSysRegs.
  intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  repeat split; rewrite writeSuccessEncoderIntAfterOutputLookupOther;
    try congruence; assumption.
Qed.

Lemma writeSuccessEncoderIntOutputMstatus regs :
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessEncoderIntAfterOutputRegs regs) writeSuccess15694Mstatus =
    Some (Val_Bool true).
Proof.
  unfold writeSuccess15694Mstatus. cbn.
  rewrite writeSuccessEncoderIntAfterOutputLookupOther;
    [|congruence|congruence]. exact.
Qed.

Lemma writeSuccessEncoderIntLoadAssumes regs (stack : bv 64) :
  regs !! "x2" = Some (RVal_Bits stack) ->
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) ->
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) ->
  islaMemoryRange (bv_unsigned stack) 16 ->
  bv_unsigned stack `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned stack ->
  bv_unsigned stack + 16 <= 0x40000000 ->
  eval_a_exp regs writeSuccess15d2cAligned = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess15d2cLower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess15d2cUpper = Some (Val_Bool true).
Proof.
  intros Hx2 Hrambase Hramsize Hrange Halign Hlower Hupper.
  destruct (writeSuccessEncoderIntStoreAssumes regs stack Hx2 Hrambase Hramsize
    Hrange Halign Hlower Hupper) as (Ha & Hl & Hu & _).
  unfold writeSuccess15d14Aligned, writeSuccess15d2cAligned in Ha |- *.
  unfold writeSuccess15d14Lower, writeSuccess15d2cLower in Hl |- *.
  unfold writeSuccess15d14Upper, writeSuccess15d2cUpper in Hu |- *.
  repeat split; assumption.
Qed.

Lemma writeSuccessEncoderInt15d34TargetExact ra :
  bv_extract 0 2 ra = BV 2 0 ->
  writeSuccess15d34Target ra = ra.
Proof.
  intros Halign.
  pose proof (writeSuccessOutputReturnTargetExact ra Halign) as Htarget.
  unfold writeSuccess15d34Target, writeSuccess101a0Target.
  unfold writeSuccess101a0Target in Htarget. exact Htarget.
Qed.

Lemma writeSuccessEncoderIntSuffixRun
    (regs : reg_map) (global : seq_global_state)
    (sp returnAddress : bv 64) :
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
  exists segments after,
    IslaInstructionRun 3
      (writeSuccess15d2cBefore (writeSuccessEncoderIntAfterOutputRegs regs) global)
      segments after /\
    (match after.1.(seq_regs) !! after.1.(seq_pc_reg) with
     | Some (RVal_Bits pc) => Some (bvn_unsigned pc)
     | _ => None
     end) = Some (bv_unsigned returnAddress) /\
    after.2.(seq_mem) = global.(seq_mem).
Proof.
  intros Hx2 Hx1 Hfacts Hread Hrange Halign HramLower HramUpper HreturnAlign Htable.
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
  exists [writeSuccess15d2cObservations
      (writeSuccessEncoderIntAfterOutputRegs regs) global mstatusBits
      (sp - BV 64 16)%bv satp returnAddress;
    writeSuccess15d30Observations regs2c global (sp - BV 64 16)%bv;
    writeSuccess15d34Observations regs30 global returnAddress],
    (writeSuccess15d34After regs30 global returnAddress).
  split.
  - econstructor; [exact Hseg2c|].
    econstructor; [exact Hseg30|].
    econstructor; [exact Hseg34|]. constructor.
  - split.
    + have Htarget := writeSuccessEncoderInt15d34TargetExact returnAddress
        HreturnAlign.
      unfold writeSuccess15d34After.
      destruct (global.(seq_instrs) !! writeSuccess15d34Target returnAddress);
        cbn; unfold writeSuccess15d34Regs; rewrite lookup_insert.
      all: rewrite Htarget; reflexivity.
    + exact Hmemory34.
Qed.

Print Assumptions writeSuccessEncoderIntOutputSysRegs.
Print Assumptions writeSuccessEncoderIntLoadAssumes.
Print Assumptions writeSuccessEncoderIntSuffixRun.
