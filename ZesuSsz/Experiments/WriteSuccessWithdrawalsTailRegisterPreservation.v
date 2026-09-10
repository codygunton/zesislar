From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsTailLookupOther regs global pointer remaining register :
  register <> "PC" ->
  register <> "x8" ->
  register <> "x9" ->
  (writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining))
    (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
      (Z_to_bv 64 (Z.of_nat (S remaining))))
    global).1.(seq_regs) !! register =
  regs !! register.
Proof.
  intros Hpc Hx8 Hx9.
  rewrite writeSuccess156e4AfterRegs.
  rewrite writeSuccess156e4RegsLookupOther; last exact Hpc.
  rewrite writeSuccess156e0RegsLookupOther; [|exact Hpc|exact Hx9].
  apply writeSuccess156dcRegsLookupOther; assumption.
Qed.

Lemma writeSuccessWithdrawalsTailRegisterFacts regs global pointer remaining :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining))
      (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
        (Z_to_bv 64 (Z.of_nat (S remaining))))
      global).1.(seq_regs).
Proof.
  intros Hfacts.
  have Hpc (rs : reg_map) (value : bv 64) :
      writeSuccessWithdrawalsOperationalRegisterFacts rs ->
      writeSuccessWithdrawalsOperationalRegisterFacts
        (<["PC" := RVal_Bits value]> rs).
  { intros H. eapply writeSuccessOperationalRegisterFactsInsertBit.
    - exact H.
    - discriminate.
    - vm_compute. repeat constructor; discriminate.
    - left. reflexivity. }
  have H1 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess156dcRegs regs pointer).
  { unfold writeSuccess156dcRegs. apply Hpc.
    apply writeSuccessOperationalRegisterFactsInsertX8. exact Hfacts. }
  have H2 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
        (Z_to_bv 64 (Z.of_nat (S remaining)))).
  { unfold writeSuccess156e0Regs. apply Hpc.
    apply writeSuccessOperationalRegisterFactsInsertX9. exact H1. }
  rewrite writeSuccess156e4AfterRegs.
  unfold writeSuccess156e4FinalRegs, writeSuccess156e4TakenRegs,
    writeSuccess156e4FallthroughRegs.
  destruct decide; apply Hpc; exact H2.
Qed.

Lemma writeSuccessWithdrawalsTailRegisterFrame regs global pointer remaining frame :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame
    (writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining))
      (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
        (Z_to_bv 64 (Z.of_nat (S remaining))))
      global).1.(seq_regs) frame.
Proof.
  intros Hframe.
  have Hpc (rs : reg_map) (value : bv 64) :
      writeSuccessWithdrawalsRegisterFrame rs frame ->
      writeSuccessWithdrawalsRegisterFrame
        (<["PC" := RVal_Bits value]> rs) frame.
  { intros H. eapply writeSuccessWithdrawalsRegisterFrameInsertBit.
    - exact H.
    - vm_compute. intuition discriminate. }
  have H1 : writeSuccessWithdrawalsRegisterFrame
      (writeSuccess156dcRegs regs pointer) frame.
  { unfold writeSuccess156dcRegs. apply Hpc.
    apply writeSuccessWithdrawalsRegisterFrameInsertX8. exact Hframe. }
  have H2 : writeSuccessWithdrawalsRegisterFrame
      (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
        (Z_to_bv 64 (Z.of_nat (S remaining)))) frame.
  { unfold writeSuccess156e0Regs. apply Hpc.
    apply writeSuccessWithdrawalsRegisterFrameInsertX9. exact H1. }
  rewrite writeSuccess156e4AfterRegs.
  unfold writeSuccess156e4FinalRegs, writeSuccess156e4TakenRegs,
    writeSuccess156e4FallthroughRegs.
  destruct decide; apply Hpc; exact H2.
Qed.

Print Assumptions writeSuccessWithdrawalsTailLookupOther.
Print Assumptions writeSuccessWithdrawalsTailRegisterFacts.
Print Assumptions writeSuccessWithdrawalsTailRegisterFrame.
