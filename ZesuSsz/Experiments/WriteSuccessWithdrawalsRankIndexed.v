From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessOccurrenceRemainingAtIndex pcs position pc :
  nth_error pcs position = Some pc ->
  writeSuccessWithdrawalsOccurrenceRemaining pc
    (count_occ Z.eq_dec (firstn position pcs) pc) pcs =
    (length pcs - position)%nat.
Proof.
  revert position. induction pcs as [|candidate pcs IH]; intros position Hnth.
  { destruct position; discriminate. }
  destruct position as [|position].
  - cbn in Hnth. injection Hnth as ->. cbn. rewrite Z.eqb_refl. reflexivity.
  - cbn in Hnth. cbn [firstn count_occ].
    destruct (Z.eq_dec candidate pc) as [->|Hne].
    + cbn. apply IH in Hnth. rewrite Z.eqb_refl. exact Hnth.
    + cbn. apply IH in Hnth.
      assert (Heqb : Z.eqb pc candidate = false) by
        (apply Z.eqb_neq; congruence).
      rewrite Heqb. exact Hnth.
Qed.

Lemma writeSuccessWithdrawalsIterationPcsLength :
  length writeSuccessWithdrawalsIterationPcs = 410%nat.
Proof. reflexivity. Qed.

Lemma writeSuccessWithdrawalsSuffixNth position pc :
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs position = Some pc ->
  nth_error writeSuccessWithdrawalsIterationPcs (342 + position) = Some pc.
Proof.
  intros Hnth. rewrite writeSuccessWithdrawalsIterationPcsMemcpyLayout.
  rewrite nth_error_app2.
  2: { cbn. lia. }
  cbn. replace (342 + position - 6)%nat with (336 + position)%nat by lia.
  exact Hnth.
Qed.

Theorem writeSuccessWithdrawalsSuffixOccurrenceAtIndex position pc :
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs position = Some pc ->
  writeSuccessWithdrawalsOccurrenceRemaining pc
    (count_occ Z.eq_dec
      (firstn (342 + position) writeSuccessWithdrawalsIterationPcs) pc)
    writeSuccessWithdrawalsIterationPcs = (68 - position)%nat.
Proof.
  intros Hnth.
  pose proof (writeSuccessWithdrawalsSuffixNth position pc Hnth) as Hremaining.
  apply writeSuccessOccurrenceRemainingAtIndex in Hremaining.
  rewrite writeSuccessWithdrawalsIterationPcsLength in Hremaining.
  replace (410 - (342 + position))%nat with (68 - position)%nat in Hremaining
    by lia.
  exact Hremaining.
Qed.

Definition writeSuccessWithdrawalsSelectedOccurrence
    (state : WriteSuccessWithdrawalsConcreteState) (pc : Z) : option nat :=
  if writeSuccessWithdrawalsPcIn pc
      [0x101d8; 0x101e0; 0x101e4; 0x101e8; 0x101ec; 0x101f0; 0x101f4]
  then
    index ← writeSuccessWithdrawalsRegisterUnsigned state "x15";
    Some (writeSuccessWithdrawalsMemcpyOccurrence pc index)
  else if writeSuccessWithdrawalsPcIn pc
      [0x15d10; 0x15d14; 0x15d18; 0x15d1c; 0x15d20;
       0x15d24; 0x15d28; 0x15d2c; 0x15d30; 0x15d34]
  then
    let returnAddress :=
      if Z.eqb pc 0x15d2c then writeSuccessWithdrawalsSavedReturn state
      else writeSuccessWithdrawalsRegisterUnsigned state "x1" in
    address ← returnAddress;
    Some (writeSuccessWithdrawalsIntegerOccurrence address)
  else if writeSuccessWithdrawalsPcIn pc
      [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0]
  then
    address ← writeSuccessWithdrawalsRegisterUnsigned state "x1";
    if Z.eqb address 0x156d0 then Some 2%nat
    else
      saved ← writeSuccessWithdrawalsSavedReturn state;
      Some (writeSuccessWithdrawalsOutputOccurrence saved)
  else Some 0%nat.

Lemma writeSuccessWithdrawalsPhaseFromSelectedOccurrence state pc occurrence :
  writeSuccessWithdrawalsConcretePc state = Some pc ->
  writeSuccessWithdrawalsSelectedOccurrence state pc = Some occurrence ->
  writeSuccessWithdrawalsPhaseRemaining state =
    writeSuccessWithdrawalsOccurrenceRemaining pc occurrence
      writeSuccessWithdrawalsIterationPcs.
Proof.
  intros Hpc Hocc. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsSelectedOccurrence in Hocc.
  destruct (writeSuccessWithdrawalsPcIn pc
    [0x101d8; 0x101e0; 0x101e4; 0x101e8; 0x101ec; 0x101f0; 0x101f4])
    eqn:Hmemcpy.
  - destruct (writeSuccessWithdrawalsRegisterUnsigned state "x15")
      eqn:Hindex; cbn in Hocc; inversion Hocc; reflexivity.
  - destruct (writeSuccessWithdrawalsPcIn pc
      [0x15d10; 0x15d14; 0x15d18; 0x15d1c; 0x15d20;
       0x15d24; 0x15d28; 0x15d2c; 0x15d30; 0x15d34]) eqn:Hinteger.
    + destruct (Z.eqb pc 0x15d2c) eqn:Hsaved.
      * destruct (writeSuccessWithdrawalsSavedReturn state) eqn:Hreturn;
          cbn in Hocc; inversion Hocc; reflexivity.
      * destruct (writeSuccessWithdrawalsRegisterUnsigned state "x1")
          eqn:Hreturn; cbn in Hocc; inversion Hocc; reflexivity.
    + destruct (writeSuccessWithdrawalsPcIn pc
        [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0]) eqn:Houtput.
      * destruct (writeSuccessWithdrawalsRegisterUnsigned state "x1")
          as [address|] eqn:Hreturn; cbn in Hocc; try discriminate.
        destruct (Z.eqb address 0x156d0) eqn:Hdirect.
        -- inversion Hocc. reflexivity.
        -- destruct (writeSuccessWithdrawalsSavedReturn state) eqn:HsavedReturn;
             cbn in Hocc; inversion Hocc; reflexivity.
      * inversion Hocc. reflexivity.
Qed.

Theorem writeSuccessWithdrawalsSuffixPhaseAtIndex state position pc :
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs position = Some pc ->
  writeSuccessWithdrawalsConcretePc state = Some pc ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (count_occ Z.eq_dec
      (firstn (342 + position) writeSuccessWithdrawalsIterationPcs) pc) ->
  writeSuccessWithdrawalsPhaseRemaining state = (68 - position)%nat.
Proof.
  intros Hnth Hpc Hocc.
  rewrite (writeSuccessWithdrawalsPhaseFromSelectedOccurrence state pc _
    Hpc Hocc).
  apply writeSuccessWithdrawalsSuffixOccurrenceAtIndex. exact Hnth.
Qed.

Theorem writeSuccessWithdrawalsSuffixRankAtIndex state remaining position pc :
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs position = Some pc ->
  writeSuccessWithdrawalsConcretePc state = Some pc ->
  writeSuccessWithdrawalsSelectedOccurrence state pc =
    Some (count_occ Z.eq_dec
      (firstn (342 + position) writeSuccessWithdrawalsIterationPcs) pc) ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  pc <> 0x156e4 ->
  pc <> 0x156e8 ->
  pc <> 0x1568c ->
  pc <> 0x15690 ->
  rank_15694 state = (410 * remaining + (68 - position))%nat.
Proof.
  intros Hnth Hpc Hocc Hx9 Hrange HnotE4 HnotE8 Hnot8c Hnot90.
  have Hphase := writeSuccessWithdrawalsSuffixPhaseAtIndex state position pc
    Hnth Hpc Hocc.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn.
  assert (H8c : Z.eqb pc 0x1568c = false) by
    (apply Z.eqb_neq; exact Hnot8c).
  assert (H90 : Z.eqb pc 0x15690 = false) by
    (apply Z.eqb_neq; exact Hnot90).
  assert (HE4 : Z.eqb pc 0x156e4 = false) by
    (apply Z.eqb_neq; exact HnotE4).
  assert (HE8 : Z.eqb pc 0x156e8 = false) by
    (apply Z.eqb_neq; exact HnotE8).
  rewrite H8c H90 HE4 HE8.
  rewrite Hphase Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Print Assumptions writeSuccessOccurrenceRemainingAtIndex.
Print Assumptions writeSuccessWithdrawalsIterationPcsLength.
Print Assumptions writeSuccessWithdrawalsSuffixNth.
Print Assumptions writeSuccessWithdrawalsSuffixOccurrenceAtIndex.
Print Assumptions writeSuccessWithdrawalsPhaseFromSelectedOccurrence.
Print Assumptions writeSuccessWithdrawalsSuffixPhaseAtIndex.
Print Assumptions writeSuccessWithdrawalsSuffixRankAtIndex.
