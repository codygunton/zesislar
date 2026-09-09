From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSuffix.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOutputEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d30.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d34.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Definition writeSuccessEncoderIntEndpointRegs
    (regs : reg_map) (sp returnAddress : bv 64) : reg_map :=
  writeSuccess15d34Regs
    (writeSuccess15d30Regs
      (writeSuccess15d2cRegs
        (writeSuccessEncoderIntAfterOutputRegs
          (writeSuccessEncoderIntRegs7 regs sp))
        returnAddress)
      (sp - BV 64 16)%bv)
    returnAddress.

Lemma writeSuccessEncoderIntEndpointLookupOther regs sp returnAddress register :
  register <> "PC" ->
  register <> "x1" ->
  register <> "x2" ->
  register <> "x5" ->
  register <> "x10" ->
  register <> "x11" ->
  writeSuccessEncoderIntEndpointRegs regs sp returnAddress !! register =
    regs !! register.
Proof.
  intros Hpc Hx1 Hx2 Hx5 Hx10 Hx11.
  unfold writeSuccessEncoderIntEndpointRegs.
  rewrite writeSuccess15d34RegsLookupOther; last exact Hpc.
  rewrite writeSuccess15d30RegsLookupOther; [|exact Hpc|exact Hx2].
  rewrite writeSuccess15d2cRegsLookupOther; [|exact Hpc|exact Hx1].
  rewrite writeSuccessEncoderIntAfterOutputLookupOther; [|exact Hpc|exact Hx5].
  apply writeSuccessEncoderIntRegs7LookupOther; assumption.
Qed.

Lemma writeSuccessEncoderIntFactsInsertX1 regs (value : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<["x1" := RVal_Bits value]> regs).
Proof.
  intros Hfacts. eapply writeSuccessOperationalRegisterFactsInsertBit.
  - exact Hfacts.
  - discriminate.
  - vm_compute. repeat constructor; discriminate.
  - right. vm_compute. tauto.
Qed.

Lemma writeSuccessEncoderIntFactsInsertX2 regs (value : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<["x2" := RVal_Bits value]> regs).
Proof.
  intros Hfacts. eapply writeSuccessOperationalRegisterFactsInsertUntrackedBit.
  - exact Hfacts.
  - discriminate.
  - vm_compute. repeat constructor; discriminate.
  - vm_compute. intuition discriminate.
Qed.

Lemma writeSuccessEncoderIntEndpointFacts regs sp returnAddress :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessEncoderIntEndpointRegs regs sp returnAddress).
Proof.
  intros Hfacts.
  have Hregs7 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs7 regs sp).
  { apply writeSuccessEncoderIntRegs7Facts. exact Hfacts. }
  have Houtput : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntAfterOutputRegs
        (writeSuccessEncoderIntRegs7 regs sp)).
  { change (writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessOutputEndpointRegs
        (writeSuccessEncoderIntRegs7 regs sp) writeSuccess15d28Link)).
    apply writeSuccessOutputEndpointFacts. exact Hregs7. }
  unfold writeSuccessEncoderIntEndpointRegs, writeSuccess15d34Regs,
    writeSuccess15d30Regs, writeSuccess15d2cRegs.
  apply writeSuccessOutputFactsInsertPc.
  apply writeSuccessOutputFactsInsertPc.
  apply writeSuccessEncoderIntFactsInsertX2.
  apply writeSuccessOutputFactsInsertPc.
  apply writeSuccessEncoderIntFactsInsertX1.
  exact Houtput.
Qed.

Lemma writeSuccessEncoderIntFrameInsertX1 regs frame (value : bv 64) :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame (<["x1" := RVal_Bits value]> regs) frame.
Proof.
  intros Hframe. eapply writeSuccessWithdrawalsRegisterFrameInsertBit.
  - exact Hframe.
  - vm_compute. intuition discriminate.
Qed.

Lemma writeSuccessEncoderIntFrameInsertX2 regs frame (value : bv 64) :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame (<["x2" := RVal_Bits value]> regs) frame.
Proof.
  intros Hframe. eapply writeSuccessWithdrawalsRegisterFrameInsertBit.
  - exact Hframe.
  - vm_compute. intuition discriminate.
Qed.

Lemma writeSuccessProtectedRegisterNotEncoderClobber register :
  register ∈ writeSuccessWithdrawalsProtectedRegisters ->
  register <> "PC" /\ register <> "x1" /\ register <> "x2" /\
  register <> "x10" /\ register <> "x11".
Proof.
  unfold writeSuccessWithdrawalsProtectedRegisters.
  intros Hin. set_solver.
Qed.

Lemma writeSuccessEncoderIntRegs7Frame regs frame sp :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame (writeSuccessEncoderIntRegs7 regs sp) frame.
Proof.
  unfold writeSuccessWithdrawalsRegisterFrame.
  intros Hframe. apply Forall_forall. intros register Hin.
  destruct (writeSuccessProtectedRegisterNotEncoderClobber register Hin) as
    (Hpc & Hx1 & Hx2 & Hx10 & Hx11).
  rewrite writeSuccessEncoderIntRegs7LookupOther;
    [|exact Hpc|exact Hx1|exact Hx2|exact Hx10|exact Hx11].
  apply (proj1 (Forall_forall _ _) Hframe). exact Hin.
Qed.

Lemma writeSuccessEncoderIntEndpointFrame regs frame sp returnAddress :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame
    (writeSuccessEncoderIntEndpointRegs regs sp returnAddress) frame.
Proof.
  intros Hframe.
  have Hregs7 := writeSuccessEncoderIntRegs7Frame regs frame sp Hframe.
  have Houtput : writeSuccessWithdrawalsRegisterFrame
      (writeSuccessEncoderIntAfterOutputRegs
        (writeSuccessEncoderIntRegs7 regs sp)) frame.
  { change (writeSuccessWithdrawalsRegisterFrame
      (writeSuccessOutputEndpointRegs
        (writeSuccessEncoderIntRegs7 regs sp) writeSuccess15d28Link) frame).
    apply writeSuccessOutputEndpointFrame. exact Hregs7. }
  unfold writeSuccessEncoderIntEndpointRegs, writeSuccess15d34Regs,
    writeSuccess15d30Regs, writeSuccess15d2cRegs.
  apply writeSuccessOutputFrameInsertPc.
  apply writeSuccessOutputFrameInsertPc.
  apply writeSuccessEncoderIntFrameInsertX2.
  apply writeSuccessOutputFrameInsertPc.
  apply writeSuccessEncoderIntFrameInsertX1.
  exact Houtput.
Qed.

Lemma writeSuccessEncoderIntEndpointExact regs global sp value returnAddress
    returnTrace :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_instrs) !!
      returnAddress = Some returnTrace ->
  writeSuccess15d34After
      (writeSuccess15d30Regs
        (writeSuccess15d2cRegs
          (writeSuccessEncoderIntAfterOutputRegs
            (writeSuccessEncoderIntRegs7 regs sp))
          returnAddress)
        (sp - BV 64 16)%bv)
      (writeSuccessEncoderIntGlobal2 global sp returnAddress value)
      returnAddress =
    (writeSuccess15694Local returnTrace
       (writeSuccessEncoderIntEndpointRegs regs sp returnAddress),
     writeSuccessEncoderIntGlobal2 global sp returnAddress value).
Proof.
  intros Halign Hlookup.
  unfold writeSuccess15d34After, writeSuccessEncoderIntEndpointRegs.
  rewrite (writeSuccessEncoderInt15d34TargetExact returnAddress Halign).
  rewrite Hlookup. reflexivity.
Qed.

Print Assumptions writeSuccessEncoderIntEndpointLookupOther.
Print Assumptions writeSuccessEncoderIntEndpointFacts.
Print Assumptions writeSuccessEncoderIntEndpointFrame.
Print Assumptions writeSuccessEncoderIntEndpointExact.
