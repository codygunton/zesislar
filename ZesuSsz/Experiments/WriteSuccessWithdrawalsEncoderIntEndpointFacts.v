From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntRecordedExact.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsEncoderIntGlobal2Instrs global sp returnAddress
    value :
  (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_instrs) =
  global.(seq_instrs).
Proof. reflexivity. Qed.

Lemma writeSuccessWithdrawalsEncoderIntEndpointGlobal regs global sp
    returnAddress value returnTrace :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp returnAddress
    value).2 = writeSuccessEncoderIntGlobal2 global sp returnAddress value.
Proof.
  intros Halign Hreturn.
  unfold writeSuccessWithdrawalsEncoderIntEndpoint, writeSuccess15d34After.
  rewrite writeSuccessEncoderInt15d34TargetExact; last exact Halign.
  rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs Hreturn. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsEncoderIntEndpointLookupOther regs global sp
    returnAddress value returnTrace register :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  register <> "PC" -> register <> "x1" -> register <> "x2" ->
  register <> "x5" -> register <> "x10" -> register <> "x11" ->
  (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp returnAddress
    value).1.(seq_regs) !! register = regs !! register.
Proof.
  intros Halign Hreturn Hpc Hx1 Hx2 Hx5 Hx10 Hx11.
  unfold writeSuccessWithdrawalsEncoderIntEndpoint, writeSuccess15d34After.
  rewrite writeSuccessEncoderInt15d34TargetExact; last exact Halign.
  rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs Hreturn. cbn.
  rewrite writeSuccess15d34RegsLookupOther; last exact Hpc.
  rewrite writeSuccess15d30RegsLookupOther; try assumption.
  rewrite writeSuccess15d2cRegsLookupOther; try assumption.
  rewrite writeSuccessEncoderIntAfterOutputLookupOther; try assumption.
  apply writeSuccessEncoderIntRegs7LookupOther; assumption.
Qed.

Lemma writeSuccessWithdrawalsEncoderIntEndpointX2 regs global sp returnAddress
    value returnTrace :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp returnAddress
    value).1.(seq_regs) !! "x2" = Some (RVal_Bits sp).
Proof.
  intros Halign Hreturn.
  unfold writeSuccessWithdrawalsEncoderIntEndpoint, writeSuccess15d34After.
  rewrite writeSuccessEncoderInt15d34TargetExact; last exact Halign.
  rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs Hreturn. cbn.
  rewrite writeSuccess15d34RegsLookupOther; last discriminate.
  unfold writeSuccess15d30Regs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert. repeat f_equal. bv_solve.
Qed.

Lemma writeSuccessWithdrawalsEncoderIntEndpointPc regs global sp returnAddress
    value returnTrace :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  (writeSuccessWithdrawalsEncoderIntEndpoint regs global sp returnAddress
    value).1.(seq_regs) !! "PC" = Some (RVal_Bits returnAddress).
Proof.
  intros Halign Hreturn.
  unfold writeSuccessWithdrawalsEncoderIntEndpoint, writeSuccess15d34After.
  rewrite writeSuccessEncoderInt15d34TargetExact; last exact Halign.
  rewrite writeSuccessWithdrawalsEncoderIntGlobal2Instrs Hreturn. cbn.
  unfold writeSuccess15d34Regs. rewrite lookup_insert.
  rewrite (writeSuccessEncoderInt15d34TargetExact returnAddress Halign).
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsEncoderIntGlobal2Instrs.
Print Assumptions writeSuccessWithdrawalsEncoderIntEndpointGlobal.
Print Assumptions writeSuccessWithdrawalsEncoderIntEndpointLookupOther.
Print Assumptions writeSuccessWithdrawalsEncoderIntEndpointX2.
Print Assumptions writeSuccessWithdrawalsEncoderIntEndpointPc.
