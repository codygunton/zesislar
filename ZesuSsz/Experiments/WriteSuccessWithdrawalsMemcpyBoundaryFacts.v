From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dc.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.

Open Scope Z_scope.

Lemma writeSuccessMemcpyBvnToBvSame n (value : bv n) :
  bvn_to_bv n (bv_to_bvn value) = Some value.
Proof.
  destruct value as [bits Hbits]. unfold bvn_to_bv. cbn.
  destruct (decide (n = n)) as [Heq|Hneq].
  - f_equal. symmetry. apply Eqdep_dec.eq_rect_eq_dec. apply N.eq_dec.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma writeSuccessMemcpyReturnAlignmentEval (regs : reg_map) (ra : bv 64) :
  regs !! "x1" = Some (RVal_Bits ra) ->
  bv_extract 0 2 ra = BV 2 0 ->
  eval_a_exp regs writeSuccess101dcAlignment = Some (Val_Bool true).
Proof.
  intros Hx1 Halign. unfold writeSuccess101dcAlignment. cbn. rewrite Hx1.
  unfold read_accessor. cbn [mbind option_bind eval_unop].
  rewrite writeSuccessMemcpyBvnToBvSame. cbn.
  rewrite bool_decide_true; first reflexivity.
  change (bv_extract 0 2 ra = BV 2 0). exact Halign.
Qed.

Lemma writeSuccessMemcpyReturnTargetExact (ra : bv 64) :
  bv_extract 0 2 ra = BV 2 0 ->
  writeSuccess101dcTarget ra = ra.
Proof.
  intros Halign.
  have Hbit : bv_extract 0 1 ra = BV 1 0.
  { bv_simplify. bv_simplify Halign.
    bitblast as i. by bitblast Halign with i. }
  unfold writeSuccess101dcTarget.
  have -> : (ra + BV 64 0)%bv = ra by bv_solve.
  apply bv_eq. bv_simplify. bv_simplify Hbit.
  bitblast as i. by bitblast Hbit with i.
Qed.

Lemma writeSuccessMemcpyInitFacts regs :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts (writeSuccess101d4Regs regs).
Proof.
  intros Hfacts. unfold writeSuccess101d4Regs.
  apply writeSuccessMemcpyOperationalInsert; [|cbn; tauto].
  apply writeSuccessMemcpyOperationalInsert; [exact Hfacts|cbn; tauto].
Qed.

Print Assumptions writeSuccessMemcpyBvnToBvSame.
Print Assumptions writeSuccessMemcpyReturnAlignmentEval.
Print Assumptions writeSuccessMemcpyReturnTargetExact.
Print Assumptions writeSuccessMemcpyInitFacts.
