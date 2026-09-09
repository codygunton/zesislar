From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156bc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntInv.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156b4SecondEncoderMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.

Open Scope Z_scope.

Definition writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal :=
  writeSuccessWithdrawalsEncoderIntEndpoint regs global sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal).

Definition writeSuccessWithdrawalsSecondEncoderEntry regs global sp withdrawal :=
  writeSuccess156bcAfter
    (writeSuccess156b8Regs
      (writeSuccess156b4Regs
        (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
        (writeSuccessWithdrawalsValidatorValue withdrawal)))
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.

Lemma writeSuccessWithdrawalsFirstEncoderEndpointBefore regs global sp withdrawal :
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal =
  writeSuccess156b4Before
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.
Proof.
  intros Htable.
  destruct (writeSuccessEncoderIntCaller156b4 global Htable) as
    (Halign & returnTrace & Hreturn).
  have Hexact := writeSuccessEncoderIntEndpointExact regs global sp
    (writeSuccessWithdrawalsIndexValue withdrawal) (Z_to_bv 64 0x156b4)
    returnTrace Halign ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs;
      exact Hreturn).
  have Hcode : global.(seq_instrs) !! Z_to_bv 64 0x156b4 = Some a156b4 by
    (apply Htable; cbn; tauto).
  have Htrace : returnTrace = a156b4 by congruence.
  subst returnTrace.
  unfold writeSuccessWithdrawalsFirstEncoderEndpoint.
  unfold writeSuccessWithdrawalsEncoderIntEndpoint.
  rewrite Hexact. reflexivity.
Qed.

Lemma writeSuccessWithdrawals156b4Assumes regs (sp : bv 64) :
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) ->
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) ->
  bv_unsigned sp `mod` 16 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp + 1792 < 0x40000000 ->
  eval_a_exp regs writeSuccess156b4Aligned = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess156b4Lower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess156b4Upper = Some (Val_Bool true).
Proof.
  intros Hsp Hbase Hsize Halign Hlower Hupper.
  have Haddress : bv_unsigned (sp + BV 64 1752)%bv = bv_unsigned sp + 1752.
  { bv_solve. }
  split.
  - unfold writeSuccess156b4Aligned. cbn. rewrite Hsp. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop eval_unop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2. apply bv_eq.
    rewrite bv_extract_unsigned. cbn. rewrite Haddress. cbn.
    change ((bv_unsigned sp + 1752) `mod` 8 = 0).
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in Halign; [|lia].
    destruct Halign as [factor Hfactor]. exists (2 * factor + 219). lia.
  - split.
    + unfold writeSuccess156b4Lower. cbn. rewrite Hsp Hbase. cbn.
      lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
        option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
        decide_rel foldl].
      repeat apply f_equal. apply bool_decide_eq_true_2.
      change (bv_unsigned (sp + BV 64 1752)%bv >=
        bv_unsigned (BV 64 0x20000000)).
      rewrite Haddress bv_unsigned_BV. cbn. lia.
    + unfold writeSuccess156b4Upper. cbn. rewrite Hsp Hbase Hsize. cbn.
      lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
        option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
        decide_rel foldl].
      repeat apply f_equal. apply bool_decide_eq_true_2.
      change (bv_unsigned (sp + BV 64 1752)%bv <= 0x3ffffff8).
      rewrite Haddress. lia.
Qed.

Lemma writeSuccessWithdrawalsFirstEncoderEndpointDirectFacts args sp pointer base
    total processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state regs0 global0 regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer =
    writeSuccess101d4Before regs0 global0 ->
  writeSuccessWithdrawalsEncoderInt156b4State regs0 global0 sp pointer current
    withdrawal = writeSuccess15d10Before regs global ->
  exists (mstatusBits satp oldDest : bv 64) (oldX1 : valu),
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) /\
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      !! "x2" = Some (RVal_Bits sp) /\
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) /\
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      !! "satp" = Some (RVal_Bits satp) /\
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      !! "x10" = Some (RVal_Bits oldDest) /\
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      !! "x1" = Some oldX1 /\
    writeSuccess156b4SysRegs
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs) /\
    eval_a_exp
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      writeSuccess15694Mstatus = Some (Val_Bool true) /\
    eval_a_exp
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      writeSuccess156b4Aligned = Some (Val_Bool true) /\
    eval_a_exp
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      writeSuccess156b4Lower = Some (Val_Bool true) /\
    eval_a_exp
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
      writeSuccess156b4Upper = Some (Val_Bool true) /\
    read_mem
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.(seq_mem)
      (bv_unsigned (writeSuccess156b4Address sp)) 8 =
      Some (bv_to_bvn (writeSuccessWithdrawalsValidatorValue withdrawal)) /\
    writeSuccessWithdrawalsInstructionTable
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).2.
Proof.
  intros Hinv Hprefix Hentry.
  have HfirstInv := writeSuccessWithdrawals156a8EncoderIntInv args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    Hinv Hprefix.
  rewrite Hentry in HfirstInv.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  destruct (writeSuccessEncoderIntCaller156b4 global Htable) as (Halign & Hcode).
  destruct Hcode as (returnTrace & HreturnTrace).
  have HendGlobal := writeSuccessWithdrawalsEncoderIntEndpointGlobal regs global
    sp (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    returnTrace Halign HreturnTrace.
  have HendExact := writeSuccessEncoderIntEndpointExact regs global sp
    (writeSuccessWithdrawalsIndexValue withdrawal) (Z_to_bv 64 0x156b4)
    returnTrace Halign ltac:(rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs;
      exact HreturnTrace).
  have HendRegs :
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs) =
      writeSuccessEncoderIntEndpointRegs regs sp (Z_to_bv 64 0x156b4).
  { unfold writeSuccessWithdrawalsFirstEncoderEndpoint.
    exact (f_equal (fun machine => machine.1.(seq_regs)) HendExact). }
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts regs by
    (unfold Inv_encoder_int in HfirstInv; cbn in HfirstInv; tauto).
  have HendFacts := writeSuccessEncoderIntEndpointFacts regs sp
    (Z_to_bv 64 0x156b4) Hfacts.
  destruct (writeSuccessMemcpyRegisterFacts _ HendFacts) as
    (mstatusBits & satp & x13 & x14 & Hx13 & Hx14 & Hmstatus & Hsatp & Hsys &
      HstoreSys & HmstatusEval).
  have Hpc := writeSuccessWithdrawalsEncoderIntEndpointPc regs global sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    returnTrace Halign HreturnTrace.
  have HspEnd := writeSuccessWithdrawalsEncoderIntEndpointX2 regs global sp
    (Z_to_bv 64 0x156b4) (writeSuccessWithdrawalsIndexValue withdrawal)
    returnTrace Halign HreturnTrace.
  have Hread := writeSuccessWithdrawalsFirstEndpointValidatorRead args sp pointer
    base total processed remaining withdrawal allBytes prefix current suffix
    scratch encoderScratch registerFrame memoryFrame priorLog state regs0 global0
    regs global Hinv Hprefix Hentry.
  have HspAlign : bv_unsigned sp `mod` 16 = 0 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hlower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hupper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have HbaseEnd :
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
        !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) by
    (rewrite HendRegs; unfold writeSuccess101e4SysRegs in Hsys; tauto).
  have HsizeEnd :
      (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
        !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) by
    (rewrite HendRegs; unfold writeSuccess101e4SysRegs in Hsys; tauto).
  have Hassumes := writeSuccessWithdrawals156b4Assumes
    (writeSuccessWithdrawalsFirstEncoderEndpoint regs global sp withdrawal).1.(seq_regs)
    sp HspEnd HbaseEnd HsizeEnd HspAlign Hlower Hupper.
  destruct Hassumes as (Haligned & HlowerEval & HupperEval).
  exists mstatusBits, satp, (sp - BV 64 16)%bv,
    (RVal_Bits (Z_to_bv 64 0x156b4)).
  split; first exact Hpc.
  split; first exact HspEnd.
  split; first (rewrite HendRegs; exact Hmstatus).
  split; first (rewrite HendRegs; exact Hsatp).
  split.
  { rewrite HendRegs. unfold writeSuccessEncoderIntEndpointRegs.
    rewrite writeSuccess15d34RegsLookupOther; last discriminate.
    rewrite writeSuccess15d30RegsLookupOther; try discriminate.
    rewrite writeSuccess15d2cRegsLookupOther; try discriminate.
    rewrite writeSuccessEncoderIntAfterOutputLookupOther; try discriminate.
    apply writeSuccessEncoderIntRegs7X10. }
  split.
  { rewrite HendRegs. unfold writeSuccessEncoderIntEndpointRegs.
    rewrite writeSuccess15d34RegsLookupOther; last discriminate.
    rewrite writeSuccess15d30RegsLookupOther; try discriminate.
    unfold writeSuccess15d2cRegs.
    rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert. reflexivity. }
  split; first (rewrite HendRegs; unfold writeSuccess156b4SysRegs,
    writeSuccess101e4SysRegs in Hsys |- *; exact Hsys).
  split; first (rewrite HendRegs; exact HmstatusEval).
  split; first exact Haligned.
  split; first exact HlowerEval.
  split; first exact HupperEval.
  split; first exact Hread.
  unfold writeSuccessWithdrawalsFirstEncoderEndpoint. rewrite HendGlobal.
  unfold writeSuccessWithdrawalsInstructionTable in Htable |- *.
  intros pc trace Hsource. apply Htable. exact Hsource.
Qed.

Print Assumptions writeSuccessWithdrawalsFirstEncoderEndpointDirectFacts.
