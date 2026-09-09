From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsOutputEndpointX2 regs sp :
  regs !! "x2" = Some (RVal_Bits sp) ->
  writeSuccessOutputEndpointRegs regs (Z_to_bv 64 0x156d0) !! "x2" =
    Some (RVal_Bits sp).
Proof.
  intros Hsp. rewrite writeSuccessOutputEndpointLookupOther; try discriminate.
  exact Hsp.
Qed.

Lemma writeSuccessWithdrawals156d0Context regs (sp : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  bv_unsigned sp `mod` 16 = 0 ->
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned sp + 1792 < 0x40000000 ->
  exists (mstatusBits satp oldDest : bv 64) (oldX1 : valu),
    regs !! "mstatus" =
      Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) /\
    regs !! "satp" = Some (RVal_Bits satp) /\
    regs !! "x10" = Some (RVal_Bits oldDest) /\
    regs !! "x1" = Some oldX1 /\
    writeSuccess156d0SysRegs regs /\
    eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess156d0Aligned = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess156d0Lower = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess156d0Upper = Some (Val_Bool true).
Proof.
  intros Hfacts Hsp Halign Hlower Hupper.
  destruct (writeSuccessOutputRegisterFacts regs Hfacts) as
    (mstatusBits & satp & oldX5 & Hx5 & Hmstatus & Hsatp & Hsys & HmstatusEval).
  destruct Hfacts as (Hoperational & Hshapes & Hgeneral).
  destruct (Hgeneral "x10" ltac:(vm_compute; tauto)) as (oldDest & Hdest).
  destruct (Hgeneral "x1" ltac:(vm_compute; tauto)) as (oldX1Bits & Hx1).
  exists mstatusBits, satp, oldDest, (RVal_Bits oldX1Bits).
  split; first exact Hmstatus.
  split; first exact Hsatp.
  split; first exact Hdest.
  split; first exact Hx1.
  split.
  { unfold WriteSuccessSegment10198.writeSuccess10198SysRegs in Hsys.
    exact Hsys. }
  split; first exact HmstatusEval.
  split.
  - unfold writeSuccess156d0Aligned. cbn. rewrite Hsp. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop eval_unop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2. apply bv_eq.
    rewrite bv_extract_unsigned. cbn.
    have Haddress : bv_unsigned (sp + BV 64 1760)%bv = bv_unsigned sp + 1760
      by bv_solve.
    rewrite Haddress. cbn.
    change ((bv_unsigned sp + 1760) `mod` 8 = 0).
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in Halign; [|lia].
    destruct Halign as [factor Hfactor]. exists (2 * factor + 220). lia.
  - split.
  + unfold writeSuccess156d0Lower. cbn. rewrite Hsp.
    unfold WriteSuccessSegment10198.writeSuccess10198SysRegs in Hsys.
    destruct Hsys as (_ & _ & Hbase & _).
    rewrite Hbase. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    have Haddress : bv_unsigned (sp + BV 64 1760)%bv = bv_unsigned sp + 1760
      by bv_solve.
    change (bv_unsigned (sp + BV 64 1760)%bv >=
      bv_unsigned (BV 64 0x20000000)).
    rewrite Haddress. change (bv_unsigned sp + 1760 >= 0x20000000).
    pose proof (bv_unsigned_in_range 64 sp). lia.
  + unfold writeSuccess156d0Upper. cbn. rewrite Hsp.
    unfold WriteSuccessSegment10198.writeSuccess10198SysRegs in Hsys.
    destruct Hsys as (_ & _ & Hbase & Hsize & _).
    rewrite Hbase Hsize. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    have Haddress : bv_unsigned (sp + BV 64 1760)%bv = bv_unsigned sp + 1760
      by bv_solve.
    change (bv_unsigned (sp + BV 64 1760)%bv <=
      bv_unsigned ((BV 64 0x20000000 + BV 64 0x20000000) - BV 64 8)%bv).
    rewrite Haddress. change (bv_unsigned sp + 1760 <= 0x3ffffff8).
    pose proof (bv_unsigned_in_range 64 sp). lia.
Qed.

Print Assumptions writeSuccessWithdrawalsOutputEndpointX2.
Print Assumptions writeSuccessWithdrawals156d0Context.
