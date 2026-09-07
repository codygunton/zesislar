From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsAfterMemcpyPcs : list Z :=
  [0x101d8; 0x101dc] ++
  [0x156a8; 0x156ac; 0x156b0] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156b4; 0x156b8; 0x156bc] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156c0; 0x156c4; 0x156c8; 0x156cc] ++
  writeSuccessWithdrawalsOutputPcs ++
  [0x156d0; 0x156d4; 0x156d8] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156dc; 0x156e0; 0x156e4].

Lemma writeSuccessWithdrawalsIterationPcsMemcpyLayout :
  writeSuccessWithdrawalsIterationPcs =
    [0x15694; 0x15698; 0x1569c; 0x156a0; 0x156a4; 0x101d4] ++
    concat (repeat writeSuccessWithdrawalsMemcpyBytePcs 48) ++
    writeSuccessWithdrawalsAfterMemcpyPcs.
Proof. reflexivity. Qed.

Lemma writeSuccessWithdrawalsAfterMemcpyPcsLength :
  length writeSuccessWithdrawalsAfterMemcpyPcs = 68%nat.
Proof. reflexivity. Qed.

Lemma writeSuccessWithdrawalsOccurrenceRemainingSkip pc occurrence prefix suffix :
  ~ In pc prefix ->
  writeSuccessWithdrawalsOccurrenceRemaining pc occurrence (prefix ++ suffix) =
    writeSuccessWithdrawalsOccurrenceRemaining pc occurrence suffix.
Proof.
  induction prefix as [|candidate prefix IH]; cbn; first reflexivity.
  intros Hnotin. destruct (Z.eqb pc candidate) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst candidate. exfalso. apply Hnotin. by left.
  - apply IH. intros Hin. apply Hnotin. by right.
Qed.

Lemma writeSuccessWithdrawalsMemcpyRepeatedLength count :
  length (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count)) =
    (7 * count)%nat.
Proof.
  induction count as [|count IH]; first reflexivity.
  cbn [writeSuccessWithdrawalsMemcpyBytePcs]. rewrite app_length IH.
  cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsOccurrence101d8Repeated count index suffix :
  (index < count)%nat ->
  writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 index
    (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
  (7 * (count - index) + length suffix)%nat.
Proof.
  revert index. induction count as [|count IH]; intros index Hindex; first lia.
  destruct index as [|index].
  - change (writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 0
      (writeSuccessWithdrawalsMemcpyBytePcs ++
       concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * (S count - 0) + length suffix)%nat).
    change (length (writeSuccessWithdrawalsMemcpyBytePcs ++
      concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * S count + length suffix)%nat).
    rewrite !app_length writeSuccessWithdrawalsMemcpyRepeatedLength.
    unfold writeSuccessWithdrawalsMemcpyBytePcs. cbn. lia.
  - change (writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 (S index)
      (writeSuccessWithdrawalsMemcpyBytePcs ++
       concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * (S count - S index) + length suffix)%nat).
    cbn [writeSuccessWithdrawalsMemcpyBytePcs
      writeSuccessWithdrawalsOccurrenceRemaining].
    apply IH. lia.
Qed.

Lemma writeSuccessWithdrawalsOccurrence101d8RepeatedBoundary count suffix :
  writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 count
    (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
  writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 0 suffix.
Proof.
  induction count as [|count IH]; first reflexivity.
  cbn [writeSuccessWithdrawalsMemcpyBytePcs
    writeSuccessWithdrawalsOccurrenceRemaining]. exact IH.
Qed.

Lemma writeSuccessWithdrawalsOccurrence101e0Repeated count index suffix :
  (index < count)%nat ->
  writeSuccessWithdrawalsOccurrenceRemaining 0x101e0 index
    (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
  (7 * (count - index) + length suffix - 1)%nat.
Proof.
  revert index. induction count as [|count IH]; intros index Hindex; first lia.
  destruct index as [|index].
  - change (writeSuccessWithdrawalsOccurrenceRemaining 0x101e0 0
      (writeSuccessWithdrawalsMemcpyBytePcs ++
       concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * S count + length suffix - 1)%nat).
    change (length ([0x101e0; 0x101e4; 0x101e8; 0x101ec; 0x101f0; 0x101f4] ++
      concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * S count + length suffix - 1)%nat).
    rewrite !app_length writeSuccessWithdrawalsMemcpyRepeatedLength. cbn. lia.
  - change (writeSuccessWithdrawalsOccurrenceRemaining 0x101e0 index
      (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * (count - index) + length suffix - 1)%nat).
    apply IH. lia.
Qed.

Lemma writeSuccessWithdrawalsOccurrence101f4Repeated count index suffix :
  (index < count)%nat ->
  writeSuccessWithdrawalsOccurrenceRemaining 0x101f4 index
    (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
  (7 * (count - index) + length suffix - 6)%nat.
Proof.
  revert index. induction count as [|count IH]; intros index Hindex; first lia.
  destruct index as [|index].
  - change (writeSuccessWithdrawalsOccurrenceRemaining 0x101f4 0
      (writeSuccessWithdrawalsMemcpyBytePcs ++
       concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * S count + length suffix - 6)%nat).
    change (length ([0x101f4] ++
      concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * S count + length suffix - 6)%nat).
    rewrite !app_length writeSuccessWithdrawalsMemcpyRepeatedLength. cbn. lia.
  - change (writeSuccessWithdrawalsOccurrenceRemaining 0x101f4 index
      (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++ suffix) =
      (7 * (count - index) + length suffix - 6)%nat).
    apply IH. lia.
Qed.

Lemma writeSuccessWithdrawalsOccurrence101d8Formula index :
  (index <= 48)%nat ->
  writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 index
    writeSuccessWithdrawalsIterationPcs = (404 - 7 * index)%nat.
Proof.
  intros Hindex. rewrite writeSuccessWithdrawalsIterationPcsMemcpyLayout.
  rewrite writeSuccessWithdrawalsOccurrenceRemainingSkip.
  2: { cbn. intuition discriminate. }
  destruct (Nat.eq_dec index 48%nat) as [->|Hne].
  - rewrite writeSuccessWithdrawalsOccurrence101d8RepeatedBoundary.
    unfold writeSuccessWithdrawalsAfterMemcpyPcs,
      writeSuccessWithdrawalsOccurrenceRemaining. cbn. reflexivity.
  - rewrite writeSuccessWithdrawalsOccurrence101d8Repeated; last lia.
    rewrite writeSuccessWithdrawalsAfterMemcpyPcsLength. lia.
Qed.

Lemma writeSuccessWithdrawalsOccurrence101e0Formula index :
  (index < 48)%nat ->
  writeSuccessWithdrawalsOccurrenceRemaining 0x101e0 index
    writeSuccessWithdrawalsIterationPcs = (403 - 7 * index)%nat.
Proof.
  intros Hindex. rewrite writeSuccessWithdrawalsIterationPcsMemcpyLayout.
  rewrite writeSuccessWithdrawalsOccurrenceRemainingSkip.
  2: { cbn. intuition discriminate. }
  rewrite writeSuccessWithdrawalsOccurrence101e0Repeated; last exact Hindex.
  rewrite writeSuccessWithdrawalsAfterMemcpyPcsLength. lia.
Qed.

Lemma writeSuccessWithdrawalsOccurrence101f4Formula index :
  (index < 48)%nat ->
  writeSuccessWithdrawalsOccurrenceRemaining 0x101f4 index
    writeSuccessWithdrawalsIterationPcs = (398 - 7 * index)%nat.
Proof.
  intros Hindex. rewrite writeSuccessWithdrawalsIterationPcsMemcpyLayout.
  rewrite writeSuccessWithdrawalsOccurrenceRemainingSkip.
  2: { cbn. intuition discriminate. }
  rewrite writeSuccessWithdrawalsOccurrence101f4Repeated; last exact Hindex.
  rewrite writeSuccessWithdrawalsAfterMemcpyPcsLength. lia.
Qed.

Lemma writeSuccessWithdrawalsMemcpyOccurrence101f4Index index :
  (0 < index)%nat ->
  writeSuccessWithdrawalsMemcpyOccurrence 0x101f4 (Z.of_nat index) =
    Nat.pred index.
Proof.
  intros Hindex. unfold writeSuccessWithdrawalsMemcpyOccurrence.
  rewrite Nat2Z.id. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPhase101d8Index state index :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d8 ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  (index <= 48)%nat ->
  writeSuccessWithdrawalsPhaseRemaining state = (404 - 7 * index)%nat.
Proof.
  intros Hpc Hx15 Hindex. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  unfold bvn_unsigned. cbn.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn [writeSuccessWithdrawalsPcIn
      writeSuccessWithdrawalsMemcpyOccurrence].
    apply writeSuccessWithdrawalsOccurrence101d8Formula. exact Hindex.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsPhase101e0Index state index :
  writeSuccessWithdrawalsConcretePc state = Some 0x101e0 ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  (index < 48)%nat ->
  writeSuccessWithdrawalsPhaseRemaining state = (403 - 7 * index)%nat.
Proof.
  intros Hpc Hx15 Hindex. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  unfold bvn_unsigned. cbn.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn [writeSuccessWithdrawalsPcIn
      writeSuccessWithdrawalsMemcpyOccurrence].
    apply writeSuccessWithdrawalsOccurrence101e0Formula. exact Hindex.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsPhase101f4Index state index :
  writeSuccessWithdrawalsConcretePc state = Some 0x101f4 ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  (0 < index <= 48)%nat ->
  writeSuccessWithdrawalsPhaseRemaining state = (405 - 7 * index)%nat.
Proof.
  intros Hpc Hx15 Hindex. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx15.
  unfold bvn_unsigned. cbn.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id.
    change (writeSuccessWithdrawalsOccurrenceRemaining 0x101f4
      (Nat.pred index) writeSuccessWithdrawalsIterationPcs =
      (405 - 7 * index)%nat).
    rewrite writeSuccessWithdrawalsOccurrence101f4Formula; last lia.
    destruct index; first lia. cbn. lia.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma rank_15694_at_101d8_index state remaining index :
  writeSuccessWithdrawalsConcretePc state = Some 0x101d8 ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  (index <= 48)%nat ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + (404 - 7 * index))%nat.
Proof.
  intros Hpc Hx15 Hindex Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101d8Index state index
    Hpc Hx15 Hindex.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn.
  rewrite Hphase. rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma rank_15694_at_101e0_index state remaining index :
  writeSuccessWithdrawalsConcretePc state = Some 0x101e0 ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  (index < 48)%nat ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + (403 - 7 * index))%nat.
Proof.
  intros Hpc Hx15 Hindex Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101e0Index state index
    Hpc Hx15 Hindex.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn.
  rewrite Hphase. rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma rank_15694_at_101f4_index state remaining index :
  writeSuccessWithdrawalsConcretePc state = Some 0x101f4 ->
  state.1.1.(seq_regs) !! "x15" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat index))) ->
  (0 < index <= 48)%nat ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + (405 - 7 * index))%nat.
Proof.
  intros Hpc Hx15 Hindex Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase101f4Index state index
    Hpc Hx15 Hindex.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9.
  unfold bvn_unsigned. cbn.
  rewrite Hphase. rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Print Assumptions writeSuccessWithdrawalsOccurrence101d8Formula.
Print Assumptions writeSuccessWithdrawalsOccurrence101e0Formula.
Print Assumptions writeSuccessWithdrawalsOccurrence101f4Formula.
Print Assumptions writeSuccessWithdrawalsPhase101d8Index.
Print Assumptions writeSuccessWithdrawalsPhase101e0Index.
Print Assumptions writeSuccessWithdrawalsPhase101f4Index.
Print Assumptions rank_15694_at_101d8_index.
Print Assumptions rank_15694_at_101e0_index.
Print Assumptions rank_15694_at_101f4_index.
