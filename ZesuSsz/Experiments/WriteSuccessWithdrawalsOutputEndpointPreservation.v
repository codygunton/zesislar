From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.

Definition writeSuccessOutputEndpointRegs (regs : reg_map) (returnAddress : bv 64) :
    reg_map :=
  writeSuccess101a0Regs (writeSuccessOutputRegs4 regs) returnAddress.

Lemma writeSuccessOutputEndpointLookupOther regs returnAddress register :
  register <> "PC" ->
  register <> "x5" ->
  writeSuccessOutputEndpointRegs regs returnAddress !! register = regs !! register.
Proof.
  intros Hpc Hx5. unfold writeSuccessOutputEndpointRegs.
  rewrite writeSuccess101a0RegsLookupOther; last exact Hpc.
  apply writeSuccessOutputRegs4LookupOther; assumption.
Qed.

Lemma writeSuccessOutputFactsInsertPc regs (value : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<["PC" := RVal_Bits value]> regs).
Proof.
  intros Hfacts. eapply writeSuccessOperationalRegisterFactsInsertBit.
  - exact Hfacts.
  - discriminate.
  - vm_compute. repeat constructor; discriminate.
  - left. reflexivity.
Qed.

Lemma writeSuccessOutputFactsInsertX5 regs (value : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<["x5" := RVal_Bits value]> regs).
Proof.
  intros Hfacts. eapply writeSuccessOperationalRegisterFactsInsertBit.
  - exact Hfacts.
  - discriminate.
  - vm_compute. repeat constructor; discriminate.
  - right. vm_compute. tauto.
Qed.

Lemma writeSuccessOutputEndpointFacts regs returnAddress :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessOutputEndpointRegs regs returnAddress).
Proof.
  intros Hfacts. unfold writeSuccessOutputEndpointRegs, writeSuccessOutputRegs4,
    writeSuccessOutputRegs3, writeSuccessOutputRegs2, writeSuccessOutputRegs1,
    writeSuccess101a0Regs, writeSuccess1019cRegs, writeSuccess10198Regs,
    writeSuccess10194Regs, writeSuccess10190Regs.
  repeat first
    [ apply writeSuccessOutputFactsInsertPc
    | apply writeSuccessOutputFactsInsertX5 ].
  exact Hfacts.
Qed.

Lemma writeSuccessOutputFrameInsertPc regs frame (value : bv 64) :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame (<["PC" := RVal_Bits value]> regs) frame.
Proof.
  intros Hframe. eapply writeSuccessWithdrawalsRegisterFrameInsertBit.
  - exact Hframe.
  - vm_compute. intuition discriminate.
Qed.

Lemma writeSuccessOutputFrameInsertX5 regs frame (value : bv 64) :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame (<["x5" := RVal_Bits value]> regs) frame.
Proof.
  intros Hframe. eapply writeSuccessWithdrawalsRegisterFrameInsertBit.
  - exact Hframe.
  - vm_compute. intuition discriminate.
Qed.

Lemma writeSuccessOutputEndpointFrame regs frame returnAddress :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame
    (writeSuccessOutputEndpointRegs regs returnAddress) frame.
Proof.
  intros Hframe. unfold writeSuccessOutputEndpointRegs, writeSuccessOutputRegs4,
    writeSuccessOutputRegs3, writeSuccessOutputRegs2, writeSuccessOutputRegs1,
    writeSuccess101a0Regs, writeSuccess1019cRegs, writeSuccess10198Regs,
    writeSuccess10194Regs, writeSuccess10190Regs.
  repeat first
    [ apply writeSuccessOutputFrameInsertPc
    | apply writeSuccessOutputFrameInsertX5 ].
  exact Hframe.
Qed.

Lemma writeSuccessOutputEndpointExact regs global returnAddress returnTrace :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  writeSuccess101a0After (writeSuccessOutputRegs4 regs) global returnAddress =
    (writeSuccess15694Local returnTrace
       (writeSuccessOutputEndpointRegs regs returnAddress), global).
Proof.
  intros Halign Hlookup.
  unfold writeSuccess101a0After, writeSuccessOutputEndpointRegs.
  rewrite (writeSuccessOutputReturnTargetExact returnAddress Halign).
  rewrite Hlookup.
  reflexivity.
Qed.

Print Assumptions writeSuccessOutputEndpointLookupOther.
Print Assumptions writeSuccessOutputEndpointFacts.
Print Assumptions writeSuccessOutputEndpointFrame.
Print Assumptions writeSuccessOutputEndpointExact.
