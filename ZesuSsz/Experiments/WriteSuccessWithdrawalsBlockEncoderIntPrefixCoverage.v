From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1cCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28Coverage.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntPrefixRunCovered
    (regs : reg_map) (global : seq_global_state)
    (value sp returnAddress : bv 64) scratch segments after :
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
  IslaInstructionRun 7 (writeSuccess15d10Before regs global) segments after ->
  exists mstatusBits satp mstatusBits2 satp2 result14 result18,
    after = writeSuccess10190Before (writeSuccessEncoderIntRegs7 regs sp)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value) /\
    segments =
      [writeSuccess15d10Observations regs global sp;
       writeSuccess15d14Observations (writeSuccessEncoderIntRegs1 regs sp) global
         mstatusBits (sp - BV 64 16)%bv satp returnAddress result14;
       writeSuccess15d18Observations (writeSuccessEncoderIntRegs2 regs sp)
         (writeSuccessEncoderIntGlobal1 global sp returnAddress) mstatusBits2
         (sp - BV 64 16)%bv satp2 value result18;
       writeSuccess15d1cObservations (writeSuccessEncoderIntRegs3 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
         (sp - BV 64 16)%bv;
       writeSuccess15d20Observations (writeSuccessEncoderIntRegs4 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value);
       writeSuccess15d24Observations (writeSuccessEncoderIntRegs5 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value);
       writeSuccess15d28Observations (writeSuccessEncoderIntRegs6 regs sp)
         (writeSuccessEncoderIntGlobal2 global sp returnAddress value)].
Proof.
  intros Hpc Hx1 Hx2 Hx10 Hscratch Hrange Halign HramLower HramUpper
    Htable Hfacts Hrun.
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
  have Hpc3 : writeSuccessEncoderIntRegs3 regs sp !! "PC" =
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
  have Hseg1c : IslaInstructionSegment
      (writeSuccess15d1cBefore (writeSuccessEncoderIntRegs3 regs sp)
        (writeSuccessEncoderIntGlobal2 global sp returnAddress value))
      (writeSuccess15d1cObservations (writeSuccessEncoderIntRegs3 regs sp)
        (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
        (sp - BV 64 16)%bv)
      (writeSuccess15d1cAfter (writeSuccessEncoderIntRegs3 regs sp)
        (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
        (sp - BV 64 16)%bv).
  { destruct (segment_15d1c_mstatus (writeSuccessEncoderIntRegs3 regs sp)
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
  inversion Hrun as [|? ? obs10 after10 ? ? Hactual10 Htail1]; subst.
  inversion Htail1 as [|? ? obs14 after14 ? ? Hactual14 Htail2]; subst.
  inversion Htail2 as [|? ? obs18 after18 ? ? Hactual18 Htail3]; subst.
  inversion Htail3 as [|? ? obs1c after1c ? ? Hactual1c Htail4]; subst.
  inversion Htail4 as [|? ? obs20 after20 ? ? Hactual20 Htail5]; subst.
  inversion Htail5 as [|? ? obs24 after24 ? ? Hactual24 Htail6]; subst.
  inversion Htail6 as [|? ? obs28 after28 ? ? Hactual28 Hzero]; subst.
  inversion Hzero; subst.
  destruct (segment_15d10_covered regs global sp (RVal_Bits sp) obs10 after10
    Hpc Hx2 Hx2 Hcode10 Hcode14 Hmstatus0 Hactual10) as
    (Hafter10 & Hobs10). subst after10.
  destruct (segment_15d14_covered (writeSuccessEncoderIntRegs1 regs sp) global
    mstatusBits (sp - BV 64 16)%bv satp returnAddress oldHigh obs14 after14
    Hregs1pc Hregs1x2 HmstatusRoot1 Hsatp1 Hregs1x1 Hsys14 Hmstatus1
    Ha14 Hl14 Hu14 (eq_ind_r (fun address =>
      read_mem global.(seq_mem) address 8 = Some oldHigh) HreadHigh Haddress14)
    Hcode14 Hcode18 Hactual14) as (result14 & Hafter14 & Hobs14).
  subst after14.
  destruct (segment_15d18_covered (writeSuccessEncoderIntRegs2 regs sp)
    (writeSuccessEncoderIntGlobal1 global sp returnAddress) mstatusBits2
    (sp - BV 64 16)%bv satp2 value oldLow obs18 after18 Hregs2pc Hregs2x2
    HmstatusRoot2 Hsatp2 Hregs2x10 Hsys18 Hmstatus2 Ha18 Hl18 Hu18
    (eq_ind_r (fun address =>
      read_mem (writeSuccessEncoderIntGlobal1 global sp returnAddress).(seq_mem)
        address 8 = Some oldLow) HreadLow1 Haddress18)
    Hcode18 Hcode1c Hactual18) as (result18 & Hafter18 & Hobs18).
  subst after18.
  destruct (segment_15d1c_covered (writeSuccessEncoderIntRegs3 regs sp)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    (sp - BV 64 16)%bv (RVal_Bits value) obs1c after1c Hpc3 Hx2_3 Hx10_3
    Hcode1c Hcode20 (proj1 Hfacts3) Hactual1c) as (Hafter1c & Hobs1c).
  subst after1c.
  destruct (segment_15d20_covered (writeSuccessEncoderIntRegs4 regs sp)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    (RVal_Bits oldX11) obs20 after20 Hpc4 HoldX11 Hcode20 Hcode24
    (proj1 Hfacts4) Hactual20) as (Hafter20 & Hobs20). subst after20.
  destruct (segment_15d24_covered (writeSuccessEncoderIntRegs5 regs sp)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
    (RVal_Bits returnAddress) obs24 after24 Hpc5 Hx1_5 Hcode24 Hcode28
    (proj1 Hfacts5) Hactual24) as (Hafter24 & Hobs24). subst after24.
  destruct (segment_15d28_covered (writeSuccessEncoderIntRegs6 regs sp)
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value) obs28 after
    Hpc6 Hx1_6 Hcode28 Hcode90 (proj1 Hfacts6) Hactual28) as
    (Hafter28 & Hobs28).
  exists mstatusBits, satp, mstatusBits2, satp2, result14, result18.
  split; first exact Hafter28.
  rewrite Hobs10 Hobs14 Hobs18 Hobs1c Hobs20 Hobs24 Hobs28. reflexivity.
Qed.

Print Assumptions writeSuccessEncoderIntPrefixRunCovered.
