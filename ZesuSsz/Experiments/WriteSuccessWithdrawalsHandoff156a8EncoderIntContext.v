From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156a8Assumes (regs : reg_map) (sp : bv 64) :
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) ->
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) ->
  bv_unsigned sp `mod` 16 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp + 1792 < 0x40000000 ->
  eval_a_exp regs writeSuccess156a8Aligned = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess156a8Lower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess156a8Upper = Some (Val_Bool true).
Proof.
  intros Hsp Hbase Hsize Halign Hlower Hupper.
  have Haddress := writeSuccessWithdrawalsPrefixDestinationUnsigned sp Hupper.
  split.
  - unfold writeSuccess156a8Aligned. cbn. rewrite Hsp. cbn.
    change (Some (Val_Bool (bool_decide
      (bv_extract 0 3 (sp + BV 64 1744)%bv = BV 3 0))) =
      Some (Val_Bool true)).
    repeat apply f_equal. apply bool_decide_eq_true_2.
    apply bv_eq. rewrite bv_extract_unsigned. cbn.
    rewrite Haddress. change ((bv_unsigned sp + 1744) `mod` 8 = 0).
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in Halign; [|lia].
    destruct Halign as [factor Hfactor]. exists (2 * factor + 218). lia.
  - split.
    + unfold writeSuccess156a8Lower. cbn. rewrite Hsp Hbase. cbn.
      lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
        option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
        decide_rel foldl].
      repeat apply f_equal. apply bool_decide_eq_true_2.
      change (bv_unsigned (sp + BV 64 1744)%bv >=
        bv_unsigned (BV 64 0x20000000)).
      rewrite Haddress bv_unsigned_BV. cbn. lia.
    + unfold writeSuccess156a8Upper. cbn. rewrite Hsp Hbase Hsize. cbn.
      lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
        option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
        decide_rel foldl].
      repeat apply f_equal. apply bool_decide_eq_true_2.
      change (bv_unsigned (sp + BV 64 1744)%bv <= 0x3ffffff8).
      rewrite Haddress. lia.
Qed.

Lemma writeSuccessWithdrawals156a8DirectFacts args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs global ->
  exists (mstatusBits satp oldDest : bv 64) (oldX1 : valu),
    writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x156a8)) /\
    writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x2" =
      Some (RVal_Bits sp) /\
    writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "mstatus" =
      Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) /\
    writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "satp" =
      Some (RVal_Bits satp) /\
    writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x10" =
      Some (RVal_Bits oldDest) /\
    writeSuccessWithdrawals156a8Regs regs global sp pointer current !! "x1" =
      Some oldX1 /\
    writeSuccess156a8SysRegs
      (writeSuccessWithdrawals156a8Regs regs global sp pointer current) /\
    eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      writeSuccess15694Mstatus = Some (Val_Bool true) /\
    eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      writeSuccess156a8Aligned = Some (Val_Bool true) /\
    eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      writeSuccess156a8Lower = Some (Val_Bool true) /\
    eval_a_exp (writeSuccessWithdrawals156a8Regs regs global sp pointer current)
      writeSuccess156a8Upper = Some (Val_Bool true) /\
    read_mem
      (writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_mem)
      (bv_unsigned (writeSuccess156a8Address sp)) 8 =
      Some (bv_to_bvn (writeSuccessWithdrawalsIndexValue withdrawal)) /\
    writeSuccessWithdrawalsInstructionTable global.
Proof.
  intros Hinv Hentry.
  have Hmemcpy := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
  rewrite Hentry in Hmemcpy.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_memcpy in Hmemcpy; cbn in Hmemcpy; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts regs by
    (unfold Inv_memcpy in Hmemcpy; cbn in Hmemcpy; tauto).
  have Hsp : regs !! "x2" = Some (RVal_Bits sp).
  { have HstateSp : state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) by
      (unfold Inv_15694 in Hinv; tauto).
    have HprefixSp :
        (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer).1.(seq_regs)
          !! "x2" = Some (RVal_Bits sp).
    { unfold writeSuccessWithdrawalsPrefixAfter,
        writeSuccessWithdrawalsPrefixStatea4,
        writeSuccessWithdrawalsPrefixStatea0,
        writeSuccessWithdrawalsPrefixState9c,
        writeSuccessWithdrawalsPrefixState98,
        writeSuccess156a4After, writeSuccess156a0After,
        writeSuccess1569cAfter, writeSuccess15698After,
        writeSuccess15694After, writeSuccess15694Local. cbn.
      rewrite writeSuccess156a4RegsLookupOther; try discriminate.
      rewrite writeSuccess156a0RegsLookupOther; try discriminate.
      rewrite writeSuccess1569cRegsLookupOther; try discriminate.
      rewrite writeSuccess15698RegsLookupOther; try discriminate.
      unfold writeSuccess15694Regs.
      repeat (rewrite lookup_insert_ne; last discriminate).
      exact HstateSp. }
    rewrite Hentry in HprefixSp. exact HprefixSp. }
  have HendFacts := writeSuccessWithdrawals156a8RegsFacts regs global sp pointer
    current Hfacts.
  destruct (writeSuccessMemcpyRegisterFacts _ HendFacts) as
    (mstatusBits & satp & x13 & x14 & Hx13 & Hx14 & Hmstatus & Hsatp & Hsys &
      HsysStore & HmstatusAssume).
  change (writeSuccess156a8SysRegs
    (writeSuccessWithdrawals156a8Regs regs global sp pointer current)) in Hsys.
  have Hbase : writeSuccessWithdrawals156a8Regs regs global sp pointer current
      !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) by
    (unfold writeSuccess156a8SysRegs in Hsys; tauto).
  have Hsize : writeSuccessWithdrawals156a8Regs regs global sp pointer current
      !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) by
    (unfold writeSuccess156a8SysRegs in Hsys; tauto).
  have HspEnd := writeSuccessWithdrawals156a8RegsX2 regs global sp pointer current Hsp.
  have Halign : bv_unsigned sp `mod` 16 = 0 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hlower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawals156a8Assumes _ sp HspEnd Hbase Hsize Halign
    Hlower Hupper) as (Haligned & HlowerEval & HupperEval).
  have HdestRead := writeSuccessWithdrawals156a8DestinationRead args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs global Hinv.
  have Hread := writeSuccessWithdrawals156a8IndexRead args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs global Hinv HdestRead.
  have Hx1base : regs !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156a8)) by
    (unfold Inv_memcpy in Hmemcpy; cbn in Hmemcpy; tauto).
  have Hx10base : regs !! "x10" = Some (RVal_Bits (sp + BV 64 1744)%bv) by
    (unfold Inv_memcpy in Hmemcpy; cbn in Hmemcpy; tauto).
  have Hx1end : writeSuccessWithdrawals156a8Regs regs global sp pointer current
      !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x156a8)).
  { unfold writeSuccessWithdrawals156a8Regs.
    rewrite writeSuccessMemcpyEndpointLookupOther; try discriminate. exact Hx1base. }
  have Hx10end : writeSuccessWithdrawals156a8Regs regs global sp pointer current
      !! "x10" = Some (RVal_Bits (sp + BV 64 1744)%bv).
  { unfold writeSuccessWithdrawals156a8Regs.
    rewrite writeSuccessMemcpyEndpointLookupOther; try discriminate. exact Hx10base. }
  exists mstatusBits, satp, (sp + BV 64 1744)%bv,
    (RVal_Bits (Z_to_bv 64 0x156a8)).
  split; first apply writeSuccessWithdrawals156a8RegsPc.
  split; first exact HspEnd.
  split; first exact Hmstatus.
  split; first exact Hsatp.
  split; first exact Hx10end.
  split; first exact Hx1end.
  split; first exact Hsys.
  split; first exact HmstatusAssume.
  split; first exact Haligned.
  split; first exact HlowerEval.
  split; first exact HupperEval.
  split; first exact Hread.
  exact Htable.
Qed.

Print Assumptions writeSuccessWithdrawals156a8Assumes.
Print Assumptions writeSuccessWithdrawals156a8DirectFacts.
