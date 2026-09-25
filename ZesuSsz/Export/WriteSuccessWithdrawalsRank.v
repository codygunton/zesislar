Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith Lia.
Require Import ZesuSsz.Export.WriteSuccessControl.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.Determinism.
Require Import isla.opsem.

Open Scope nat_scope.

(** The withdrawal loop keeps its remaining count in x9 at 0x15694.
    The value zero selects the exit at 0x156e8. *)
Definition writeSuccessWithdrawalsMachineRank (theta : seq_local_state) : nat :=
  match seq_regs theta !! "x9" with
  | Some (RVal_Bits value) => Z.to_nat (bvn_unsigned value)
  | _ => 0
  end.

Lemma writeSuccessWithdrawalsRankFromCounter theta remaining :
  seq_regs theta !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  (Z.of_nat remaining < bv_modulus 64)%Z ->
  writeSuccessWithdrawalsMachineRank theta = remaining.
Proof.
  intros Hcounter Hrange.
  unfold writeSuccessWithdrawalsMachineRank. rewrite Hcounter.
  simpl.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat remaining))) = remaining).
  rewrite Z_to_bv_small; lia.
Qed.

Lemma writeSuccessWithdrawalsRankMatchesSuffix theta
    (suffix : list (bv 8)) remaining :
  seq_regs theta !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  (Z.of_nat remaining < bv_modulus 64)%Z ->
  length suffix = 48 * remaining ->
  length suffix = 48 * writeSuccessWithdrawalsMachineRank theta.
Proof.
  intros Hcounter Hrange Hlength.
  rewrite (writeSuccessWithdrawalsRankFromCounter theta remaining Hcounter Hrange).
  exact Hlength.
Qed.

(** The back-edge proof still must establish these register facts from
    the verified executor.  This lemma proves the rank step they imply. *)
Lemma writeSuccessWithdrawalsBackEdgeRank before after remaining :
  seq_regs before !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S (S remaining))))) ->
  seq_regs after !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S (S remaining)) < bv_modulus 64)%Z ->
  writeSuccessWithdrawalsMachineRank after <
    writeSuccessWithdrawalsMachineRank before.
Proof.
  intros Hbefore Hafter Hrange.
  rewrite (writeSuccessWithdrawalsRankFromCounter before _ Hbefore Hrange).
  rewrite (writeSuccessWithdrawalsRankFromCounter after _ Hafter); lia.
Qed.

Lemma writeSuccessWithdrawalsRankZeroAtExit theta :
  seq_regs theta !! "x9" = Some (RVal_Bits (BV 64 0)) ->
  writeSuccessWithdrawalsMachineRank theta = 0.
Proof.
  intros Hcounter.
  unfold writeSuccessWithdrawalsMachineRank. rewrite Hcounter.
  reflexivity.
Qed.

Lemma writeSuccessWithdrawalsRankSuccessorUnique pc trace regs sigma
    labels1 theta1 sigma1 labels2 theta2 sigma2 :
  writeSuccessControlBoundary pc trace regs sigma ->
  executor_deterministicb trace regs sigma = true ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma
    labels1 theta1 sigma1 ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma
    labels2 theta2 sigma2 ->
  writeSuccessWithdrawalsMachineRank theta1 =
    writeSuccessWithdrawalsMachineRank theta2.
Proof.
  intros Hboundary Hdet Hfirst Hsecond.
  destruct (writeSuccess_completed_successor_unique _ _ _ _ _ _ _ _ _ _
    Hboundary Hdet Hfirst Hsecond) as [Hregs _].
  unfold writeSuccessWithdrawalsMachineRank.
  rewrite Hregs. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsRankFromCounter.
Print Assumptions writeSuccessWithdrawalsRankMatchesSuffix.
Print Assumptions writeSuccessWithdrawalsBackEdgeRank.
Print Assumptions writeSuccessWithdrawalsRankZeroAtExit.
Print Assumptions writeSuccessWithdrawalsRankSuccessorUnique.
