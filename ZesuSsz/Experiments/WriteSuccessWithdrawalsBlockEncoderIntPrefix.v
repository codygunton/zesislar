From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import IslaTraces.write_success_07.a15d14.
Require Import IslaTraces.write_success_07.a15d18.
Require Import IslaTraces.write_success_07.a15d1c.
Require Import IslaTraces.write_success_07.a15d20.
Require Import IslaTraces.write_success_07.a15d24.
Require Import IslaTraces.write_success_07.a15d28.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntInstructionFacts global :
  writeSuccessWithdrawalsInstructionTable global ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d20 = Some a15d20 /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d24 = Some a15d24 /\
  global.(seq_instrs) !! Z_to_bv 64 0x15d28 = Some a15d28 /\
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190.
Proof.
  intros Htable. repeat split; apply Htable;
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap; cbn; tauto.
Qed.

Lemma writeSuccessEncoderIntFirstStorePreservesLow global
    (sp returnAddress : bv 64) low :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  read_mem global.(seq_mem) (bv_unsigned sp - 16) 8%N = Some low ->
  read_mem (writeSuccessEncoderIntGlobal1 global sp returnAddress).(seq_mem)
    (bv_unsigned sp - 16) 8%N = Some low.
Proof.
  intros Hrange Hread. unfold read_mem in Hread |- *.
  unfold writeSuccessEncoderIntGlobal1, writeSuccess15d14Global,
    writeSuccess15d14Memory, writeSuccess15d14Address,
    writeSuccess15d14Bytes. cbn.
  replace (sp - BV 64 16 + BV 64 8)%bv with
    (Z_to_bv 64 (bv_unsigned sp - 8)) by (apply bv_eq; bv_solve).
  have HwriteRange : islaMemoryRange (bv_unsigned sp - 8)
      (length (bv_to_little_endian 8 8 (bv_unsigned returnAddress))).
  { rewrite length_bv_to_little_endian; [|lia].
    unfold islaMemoryRange in Hrange. unfold islaMemoryRange. lia.
  }
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned sp - 8)
      (length (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
      (bv_unsigned sp - 16) 8.
  { rewrite length_bv_to_little_endian; [|lia].
    unfold islaMemoryRangesDisjoint. lia. }
  pose proof (read_mem_list_write_mem_list_disjoint_eq global.(seq_mem)
    (bv_unsigned sp - 8)
    (bv_to_little_endian 8 8 (bv_unsigned returnAddress))
    (bv_unsigned sp - 16) 8 HwriteRange Hdisjoint) as Hskip.
  change (read_mem_list
    (write_mem_list global.(seq_mem) (Z_to_bv 64 (bv_unsigned sp - 8))
      (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
    (bv_unsigned sp - 16) 8%N =
    read_mem_list global.(seq_mem) (bv_unsigned sp - 16) 8%N) in Hskip.
  rewrite Hskip. exact Hread.
Qed.

Lemma writeSuccessEncoderIntPrefixRun
    (regs : reg_map) (global : seq_global_state)
    (value sp returnAddress : bv 64) scratch :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d10)) ->
  regs !! "x1" = Some (RVal_Bits returnAddress) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  read_mem_list global.(seq_mem) (bv_unsigned sp - 16) 16%N = Some scratch ->
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  bv_unsigned sp `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 0x40000000 ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  exists segments,
    IslaInstructionRun 7 (writeSuccess15d10Before regs global) segments
      (writeSuccess10190Before (writeSuccessEncoderIntRegs7 regs sp)
        (writeSuccessEncoderIntGlobal2 global sp returnAddress value)).
Proof.
  intros Hpc Hx1 Hx2 Hx10 Hscratch Hrange Halign HramLower HramUpper
    Htable Hfacts.
  destruct (writeSuccessEncoderIntInstructionFacts global Htable) as
    (Hcode10 & Hcode14 & Hcode18 & Hcode1c & Hcode20 & Hcode24 & Hcode28 &
     Hcode90).
  destruct (writeSuccessEncoderIntInitialReads global.(seq_mem) sp scratch Hscratch)
    as (low & high & oldLow & oldHigh & HscratchSplit & HlowLength &
      HhighLength & HreadLow & HreadHigh).
  destruct (writeSuccessEncoderIntPrefixFacts regs sp Hfacts) as
    (Hfacts1 & Hfacts2 & Hfacts3 & Hfacts4 & Hfacts5 & Hfacts6 & Hfacts7).
  have HstackRange : islaMemoryRange (bv_unsigned (sp - BV 64 16)%bv) 16.
  { rewrite writeSuccessEncoderIntStackUnsigned; assumption. }
  have HstackAlign : bv_unsigned (sp - BV 64 16)%bv `mod` 8 = 0.
  { rewrite writeSuccessEncoderIntStackUnsigned; [|assumption]. lia. }
  have HstackLower : 0x20000000 <= bv_unsigned (sp - BV 64 16)%bv.
  { rewrite writeSuccessEncoderIntStackUnsigned; assumption. }
  have HstackUpper : bv_unsigned (sp - BV 64 16)%bv + 16 <= 0x40000000.
  { rewrite writeSuccessEncoderIntStackUnsigned; [|assumption]. lia. }
  have Hmstatus0 : eval_a_exp regs writeSuccess15d10Mstatus = Some (Val_Bool true).
  { exact (proj1 Hfacts). }
  have Hseg10 := proj1 (segment_15d10 regs global sp (RVal_Bits sp)
    Hpc Hx2 Hx2 Hcode10 Hcode14 Hmstatus0).
  have Hregs1x1 : writeSuccessEncoderIntRegs1 regs sp !! "x1" =
      Some (RVal_Bits returnAddress).
  { unfold writeSuccessEncoderIntRegs1, writeSuccess15d10Regs.
    rewrite lookup_insert_ne; [|congruence]. rewrite lookup_insert_ne;
      [exact Hx1|congruence]. }
  have Hregs1x2 : writeSuccessEncoderIntRegs1 regs sp !! "x2" =
      Some (RVal_Bits (sp - BV 64 16)%bv).
  { unfold writeSuccessEncoderIntRegs1, writeSuccess15d10Regs.
    rewrite lookup_insert_ne; [|congruence]. rewrite lookup_insert.
    rewrite writeSuccessEncoderIntStackExact. reflexivity. }
  destruct (writeSuccessEncoderIntStoreFacts (writeSuccessEncoderIntRegs1 regs sp)
    (sp - BV 64 16)%bv Hregs1x2 Hfacts1 HstackRange HstackAlign HstackLower
    HstackUpper) as
    (mstatusBits & satp & HmstatusRoot1 & Hsatp1 & Hsys14 & Hsys18a &
     Hmstatus1 & Ha14 & Hl14 & Hu14 & Ha18a & Hl18a & Hu18a).
  have Hregs1pc : writeSuccessEncoderIntRegs1 regs sp !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15d14)).
  { unfold writeSuccessEncoderIntRegs1, writeSuccess15d10Regs.
    rewrite lookup_insert. reflexivity. }
  have Haddress14 :
      bv_unsigned (writeSuccess15d14Address (sp - BV 64 16)%bv) =
      bv_unsigned sp - 8.
  { unfold writeSuccess15d14Address. apply Z.le_antisymm; bv_solve. }
  have Hseg14 := proj1 (segment_15d14 (writeSuccessEncoderIntRegs1 regs sp)
    global mstatusBits (sp - BV 64 16)%bv satp returnAddress false oldHigh
    Hregs1pc Hregs1x2 HmstatusRoot1 Hsatp1 Hregs1x1 Hsys14 Hmstatus1
    Ha14 Hl14 Hu14 (eq_ind_r (fun address =>
      read_mem global.(seq_mem) address 8 = Some oldHigh) HreadHigh Haddress14)
    Hcode14 Hcode18).
  have Hregs2x2 : writeSuccessEncoderIntRegs2 regs sp !! "x2" =
      Some (RVal_Bits (sp - BV 64 16)%bv).
  { unfold writeSuccessEncoderIntRegs2, writeSuccess15d14Regs.
    rewrite lookup_insert_ne; [exact Hregs1x2|congruence]. }
  have Hregs2x10 : writeSuccessEncoderIntRegs2 regs sp !! "x10" =
      Some (RVal_Bits value).
  { unfold writeSuccessEncoderIntRegs2, writeSuccess15d14Regs,
      writeSuccessEncoderIntRegs1, writeSuccess15d10Regs.
    rewrite !lookup_insert_ne; try congruence. exact Hx10. }
  destruct (writeSuccessEncoderIntStoreFacts (writeSuccessEncoderIntRegs2 regs sp)
    (sp - BV 64 16)%bv Hregs2x2 Hfacts2 HstackRange HstackAlign HstackLower
    HstackUpper) as
    (mstatusBits2 & satp2 & HmstatusRoot2 & Hsatp2 & Hsys14b & Hsys18 &
     Hmstatus2 & Ha14b & Hl14b & Hu14b & Ha18 & Hl18 & Hu18).
  have Hregs2pc : writeSuccessEncoderIntRegs2 regs sp !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15d18)).
  { unfold writeSuccessEncoderIntRegs2, writeSuccess15d14Regs.
    rewrite lookup_insert. reflexivity. }
  have HreadLow1 := writeSuccessEncoderIntFirstStorePreservesLow global sp
    returnAddress oldLow Hrange HreadLow.
  have Haddress18 :
      bv_unsigned (writeSuccess15d18Address (sp - BV 64 16)%bv) =
      bv_unsigned sp - 16.
  { unfold writeSuccess15d18Address. apply Z.le_antisymm; bv_solve. }
  have Hseg18 := proj1 (segment_15d18 (writeSuccessEncoderIntRegs2 regs sp)
    (writeSuccessEncoderIntGlobal1 global sp returnAddress) mstatusBits2
    (sp - BV 64 16)%bv satp2 value false oldLow Hregs2pc Hregs2x2
    HmstatusRoot2 Hsatp2 Hregs2x10 Hsys18 Hmstatus2 Ha18 Hl18 Hu18
    (eq_ind_r (fun address =>
      read_mem (writeSuccessEncoderIntGlobal1 global sp returnAddress).(seq_mem)
        address 8 = Some oldLow) HreadLow1 Haddress18)
    Hcode18 Hcode1c).
  (* The remaining five register-only segments use the exact generated states. *)
  have Hseg1c : IslaInstructionSegment
      (writeSuccess15d1cBefore (writeSuccessEncoderIntRegs3 regs sp)
        (writeSuccessEncoderIntGlobal2 global sp returnAddress value))
      (writeSuccess15d1cObservations (writeSuccessEncoderIntRegs3 regs sp)
        (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
        (sp - BV 64 16)%bv)
      (writeSuccess15d1cAfter (writeSuccessEncoderIntRegs3 regs sp)
        (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
        (sp - BV 64 16)%bv).
  { have Hpc3 : writeSuccessEncoderIntRegs3 regs sp !! "PC" =
        Some (RVal_Bits (Z_to_bv 64 0x15d1c)).
    { unfold writeSuccessEncoderIntRegs3, writeSuccess15d18Regs.
      rewrite lookup_insert. reflexivity. }
    have Hx2_3 : writeSuccessEncoderIntRegs3 regs sp !! "x2" =
        Some (RVal_Bits (sp - BV 64 16)%bv).
    { unfold writeSuccessEncoderIntRegs3, writeSuccess15d18Regs.
      rewrite lookup_insert_ne; [exact Hregs2x2|congruence]. }
    have Hx10_3 : writeSuccessEncoderIntRegs3 regs sp !! "x10" =
        Some (RVal_Bits value).
    { unfold writeSuccessEncoderIntRegs3, writeSuccess15d18Regs.
      rewrite lookup_insert_ne; [exact Hregs2x10|congruence]. }
    destruct (segment_15d1c_mstatus (writeSuccessEncoderIntRegs3 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
      (sp - BV 64 16)%bv (RVal_Bits value) Hpc3 Hx2_3 Hx10_3
      Hcode1c Hcode20 (proj1 Hfacts3)) as (Hsegment & _).
    exact Hsegment. }
  have Hpc4 : writeSuccessEncoderIntRegs4 regs sp !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15d20)).
  { unfold writeSuccessEncoderIntRegs4, writeSuccess15d1cRegs.
    rewrite lookup_insert. reflexivity. }
  destruct (proj2 (proj2 Hfacts4) "x11" ltac:(cbn; tauto)) as
    (oldX11 & HoldX11).
  destruct (segment_15d20 (writeSuccessEncoderIntRegs4 regs sp)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    (RVal_Bits oldX11) Hpc4 HoldX11 Hcode20 Hcode24 (proj1 Hfacts4)) as
    (Hseg20 & _).
  have Hpc5 : writeSuccessEncoderIntRegs5 regs sp !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15d24)).
  { unfold writeSuccessEncoderIntRegs5, writeSuccess15d20Regs.
    rewrite lookup_insert. reflexivity. }
  have Hx1_5 : writeSuccessEncoderIntRegs5 regs sp !! "x1" =
      Some (RVal_Bits returnAddress).
  { unfold writeSuccessEncoderIntRegs5, writeSuccessEncoderIntRegs4,
      writeSuccessEncoderIntRegs3, writeSuccessEncoderIntRegs2,
      writeSuccessEncoderIntRegs1, writeSuccess15d20Regs,
      writeSuccess15d1cRegs, writeSuccess15d18Regs,
      writeSuccess15d14Regs, writeSuccess15d10Regs.
    repeat (rewrite lookup_insert_ne; [|congruence]). exact Hx1. }
  destruct (segment_15d24_mstatus (writeSuccessEncoderIntRegs5 regs sp)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    (RVal_Bits returnAddress) Hpc5 Hx1_5 Hcode24 Hcode28
    (proj1 Hfacts5)) as (Hseg24 & _).
  have Hpc6 : writeSuccessEncoderIntRegs6 regs sp !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15d28)).
  { unfold writeSuccessEncoderIntRegs6, writeSuccess15d24Regs.
    rewrite lookup_insert. reflexivity. }
  have Hx1_6 : writeSuccessEncoderIntRegs6 regs sp !! "x1" =
      Some (RVal_Bits writeSuccess15d28Ra).
  { unfold writeSuccessEncoderIntRegs6, writeSuccess15d24Regs.
    rewrite lookup_insert_ne; [|congruence]. rewrite lookup_insert. reflexivity. }
  destruct (segment_15d28_mstatus (writeSuccessEncoderIntRegs6 regs sp)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    Hpc6 Hx1_6 Hcode28 Hcode90 (proj1 Hfacts6)) as (Hseg28 & _).
  exists [writeSuccess15d10Observations regs global sp;
    writeSuccess15d14Observations (writeSuccessEncoderIntRegs1 regs sp) global
      mstatusBits (sp - BV 64 16)%bv satp returnAddress false;
    writeSuccess15d18Observations (writeSuccessEncoderIntRegs2 regs sp)
      (writeSuccessEncoderIntGlobal1 global sp returnAddress) mstatusBits2
      (sp - BV 64 16)%bv satp2 value false;
    writeSuccess15d1cObservations (writeSuccessEncoderIntRegs3 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
      (sp - BV 64 16)%bv;
    writeSuccess15d20Observations (writeSuccessEncoderIntRegs4 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value);
    writeSuccess15d24Observations (writeSuccessEncoderIntRegs5 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value);
    writeSuccess15d28Observations (writeSuccessEncoderIntRegs6 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value)].
  econstructor; [exact Hseg10|].
  econstructor; [exact Hseg14|].
  econstructor; [exact Hseg18|].
  econstructor; [exact Hseg1c|].
  econstructor; [exact Hseg20|].
  econstructor; [exact Hseg24|].
  econstructor; [exact Hseg28|].
  constructor.
Qed.

Print Assumptions writeSuccessEncoderIntFirstStorePreservesLow.
Print Assumptions writeSuccessEncoderIntPrefixRun.
