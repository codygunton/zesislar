From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Import ListNotations.
Open Scope Z_scope.

Fixpoint writeSuccessWithdrawalsOccurrenceRemaining
    (pc : Z) (occurrence : nat) (pcs : list Z) : nat :=
  match pcs with
  | [] => 0%nat
  | candidate :: rest =>
      if Z.eqb pc candidate then
        match occurrence with
        | O => length pcs
        | S next => writeSuccessWithdrawalsOccurrenceRemaining pc next rest
        end
      else writeSuccessWithdrawalsOccurrenceRemaining pc occurrence rest
  end.

Definition writeSuccessWithdrawalsRegisterUnsigned
    (state : WriteSuccessWithdrawalsConcreteState) (register : string) : option Z :=
  match state.1.1.(seq_regs) !! register with
  | Some (RVal_Bits value) => Some (bvn_unsigned value)
  | _ => None
  end.

Definition writeSuccessWithdrawalsSavedReturn
    (state : WriteSuccessWithdrawalsConcreteState) : option Z :=
  match writeSuccessWithdrawalsRegisterUnsigned state "x2" with
  | Some currentSp =>
      match read_mem state.1.2.(seq_mem) (currentSp + 8) 8%N with
      | Some value => Some (bvn_unsigned value)
      | None => None
      end
  | None => None
  end.

Definition writeSuccessWithdrawalsIntegerOccurrence (returnAddress : Z) : nat :=
  if Z.eqb returnAddress 0x156b4 then 0%nat
  else if Z.eqb returnAddress 0x156c0 then 1%nat
  else if Z.eqb returnAddress 0x156dc then 2%nat
  else 3%nat.

Definition writeSuccessWithdrawalsOutputOccurrence (returnAddress : Z) : nat :=
  if Z.eqb returnAddress 0x156b4 then 0%nat
  else if Z.eqb returnAddress 0x156c0 then 1%nat
  else if Z.eqb returnAddress 0x156d0 then 2%nat
  else if Z.eqb returnAddress 0x156dc then 3%nat
  else 4%nat.

Definition writeSuccessWithdrawalsMemcpyOccurrence
    (pc index : Z) : nat :=
  if Z.eqb pc 0x101f0 || Z.eqb pc 0x101f4
  then Nat.pred (Z.to_nat index)
  else Z.to_nat index.

Definition writeSuccessWithdrawalsPcIn (pc : Z) (pcs : list Z) : bool :=
  existsb (Z.eqb pc) pcs.

Definition writeSuccessWithdrawalsPhaseRemaining
    (state : WriteSuccessWithdrawalsConcreteState) : nat :=
  match writeSuccessWithdrawalsConcretePc state with
  | None => 0%nat
  | Some pc =>
      let occurrence :=
        if writeSuccessWithdrawalsPcIn pc
            [0x101d8; 0x101e0; 0x101e4; 0x101e8;
             0x101ec; 0x101f0; 0x101f4] then
          match writeSuccessWithdrawalsRegisterUnsigned state "x15" with
          | Some index => writeSuccessWithdrawalsMemcpyOccurrence pc index
          | None => 49%nat
          end
        else if writeSuccessWithdrawalsPcIn pc
            [0x15d10; 0x15d14; 0x15d18; 0x15d1c; 0x15d20;
             0x15d24; 0x15d28; 0x15d2c; 0x15d30; 0x15d34] then
          let returnAddress :=
            if Z.eqb pc 0x15d2c then writeSuccessWithdrawalsSavedReturn state
            else writeSuccessWithdrawalsRegisterUnsigned state "x1" in
          match returnAddress with
          | Some returnAddress =>
              writeSuccessWithdrawalsIntegerOccurrence returnAddress
          | None => 3%nat
          end
        else if writeSuccessWithdrawalsPcIn pc
            [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0] then
          match writeSuccessWithdrawalsRegisterUnsigned state "x1" with
          | Some returnAddress =>
              if Z.eqb returnAddress 0x156d0 then 2%nat
              else
                match writeSuccessWithdrawalsSavedReturn state with
                | Some savedReturn =>
                    writeSuccessWithdrawalsOutputOccurrence savedReturn
                | None => 4%nat
                end
          | None => 4%nat
          end
        else 0%nat in
      writeSuccessWithdrawalsOccurrenceRemaining pc occurrence
        writeSuccessWithdrawalsIterationPcs
  end.

Definition rank_15694
    (state : WriteSuccessWithdrawalsConcreteState) : nat :=
  match writeSuccessWithdrawalsConcretePc state,
    writeSuccessWithdrawalsRegisterUnsigned state "x9" with
  | Some pc, Some counter =>
      if Z.eqb pc 0x1568c then (410 * Z.to_nat counter + 2)%nat
      else if Z.eqb pc 0x15690 then (410 * Z.to_nat counter + 1)%nat
      else if Z.eqb pc 0x156e4 then (410 * Z.to_nat counter + 1)%nat
      else if Z.eqb pc 0x156e8 then 0%nat
      else (410 * Nat.pred (Z.to_nat counter) +
        writeSuccessWithdrawalsPhaseRemaining state)%nat
  | _, _ => 0%nat
  end.

Lemma writeSuccessWithdrawalsPhase15694 state :
  writeSuccessWithdrawalsConcretePc state = Some 0x15694 ->
  writeSuccessWithdrawalsPhaseRemaining state = 410%nat.
Proof.
  intros Hpc. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. vm_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPhase15698 state :
  writeSuccessWithdrawalsConcretePc state = Some 0x15698 ->
  writeSuccessWithdrawalsPhaseRemaining state = 409%nat.
Proof.
  intros Hpc. unfold writeSuccessWithdrawalsPhaseRemaining.
  rewrite Hpc. vm_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawalsPhaseChecks :
  writeSuccessWithdrawalsMemcpyOccurrence 0x101f4 1 = 0%nat /\
  writeSuccessWithdrawalsMemcpyOccurrence 0x101d8 1 = 1%nat /\
  writeSuccessWithdrawalsIntegerOccurrence 0x156dc = 2%nat /\
  writeSuccessWithdrawalsOutputOccurrence 0x156d0 = 2%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x101d4 0
      writeSuccessWithdrawalsIterationPcs = 405%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 0
      writeSuccessWithdrawalsIterationPcs = 404%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x101d8 48
      writeSuccessWithdrawalsIterationPcs = 68%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x15d10 0
      writeSuccessWithdrawalsIterationPcs = 63%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x15d10 1
      writeSuccessWithdrawalsIterationPcs = 45%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x15d10 2
      writeSuccessWithdrawalsIterationPcs = 18%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x10190 0
      writeSuccessWithdrawalsIterationPcs = 56%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x10190 1
      writeSuccessWithdrawalsIterationPcs = 38%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x10190 2
      writeSuccessWithdrawalsIterationPcs = 26%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x10190 3
      writeSuccessWithdrawalsIterationPcs = 11%nat /\
  writeSuccessWithdrawalsOccurrenceRemaining 0x156e4 0
      writeSuccessWithdrawalsIterationPcs = 1%nat.
Proof. vm_compute. repeat split. Qed.

Lemma Inv_1568c_total_range args sp base total allBytes scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_1568c args sp base total allBytes scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  (Z.of_nat total < 2 ^ 64)%Z.
Proof.
  unfold Inv_1568c. intros Hinv.
  have Hrepresentation : writeSuccessConcreteRepresentation
      (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) by tauto.
  have Htotal : total = length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) by tauto.
  have Hvalid : writeSuccessObservationValid
      (successDecoded WriteSuccessObservation args).
  { unfold writeSuccessConcreteRepresentation in Hrepresentation. tauto. }
  have Hwithdrawals : writeSuccessListValid
      writeSuccessWithdrawalObservationValid
      (observationWithdrawals (successDecoded WriteSuccessObservation args)).
  { unfold writeSuccessObservationValid in Hvalid. tauto. }
  unfold writeSuccessListValid, writeSuccessLengthValid in Hwithdrawals.
  rewrite Htotal. tauto.
Qed.

Lemma Inv_1568c_rank args sp base total allBytes scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_1568c args sp base total allBytes scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  rank_15694 state = (410 * total + 2)%nat.
Proof.
  intros Hinv.
  have Hpc : writeSuccessWithdrawalsConcretePc state = Some 0x1568c by
    (unfold Inv_1568c in Hinv; tauto).
  have Hx9 : state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat total))) by
    (unfold Inv_1568c in Hinv; tauto).
  have Hrange := Inv_1568c_total_range _ _ _ _ _ _ _ _ _ _ _ Hinv.
  unfold rank_15694, writeSuccessWithdrawalsRegisterUnsigned.
  rewrite Hpc Hx9. cbn.
  change (410 * Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat total))) + 2 =
    410 * total + 2)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. lia.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma Inv_15694_counter_range args sp pointer base total processed remaining
    withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z.
Proof.
  unfold Inv_15694. intros Hinv.
  have Hrepresentation : writeSuccessConcreteRepresentation
      (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) by tauto.
  have Htotal : total = length (observationWithdrawals
      (successDecoded WriteSuccessObservation args)) by tauto.
  have Hparts : total = (processed + S remaining)%nat by tauto.
  have Hvalid : writeSuccessObservationValid
      (successDecoded WriteSuccessObservation args).
  { unfold writeSuccessConcreteRepresentation in Hrepresentation. tauto. }
  have Hwithdrawals : writeSuccessListValid
      writeSuccessWithdrawalObservationValid
      (observationWithdrawals (successDecoded WriteSuccessObservation args)).
  { unfold writeSuccessObservationValid in Hvalid. tauto. }
  unfold writeSuccessListValid, writeSuccessLengthValid in Hwithdrawals.
  destruct Hwithdrawals as [Hwithdrawals _].
  rewrite <- Htotal in Hwithdrawals.
  have Hle : (S remaining <= total)%nat by lia.
  apply Nat2Z.inj_le in Hle. lia.
Qed.

Lemma Inv_15694_rank args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  rank_15694 state = (410 * S remaining)%nat.
Proof.
  intros Hinv.
  have Hpc : writeSuccessWithdrawalsConcretePc state = Some 0x15694 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hx9 : state.1.1.(seq_regs) !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) by
    (unfold Inv_15694 in Hinv; tauto).
  have Hrange := Inv_15694_counter_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hinv.
  have Hphase := writeSuccessWithdrawalsPhase15694 state Hpc.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 410 =
    410 * S remaining)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. lia.
  - unfold bv_modulus. cbn. lia.
Qed.

Lemma rank_15694_at_15698 state remaining :
  writeSuccessWithdrawalsConcretePc state = Some 0x15698 ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  rank_15694 state = (410 * remaining + 409)%nat.
Proof.
  intros Hpc Hx9 Hrange.
  have Hphase := writeSuccessWithdrawalsPhase15698 state Hpc.
  unfold rank_15694. rewrite Hpc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx9. cbn.
  rewrite Hphase.
  change (410 * Nat.pred
      (Z.to_nat (bv_unsigned (Z_to_bv 64 (Z.of_nat (S remaining))))) + 409 =
    410 * remaining + 409)%nat.
  rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id. cbn. reflexivity.
  - unfold bv_modulus. cbn. lia.
Qed.

Print Assumptions writeSuccessWithdrawalsPhase15694.
Print Assumptions writeSuccessWithdrawalsPhase15698.
Print Assumptions writeSuccessWithdrawalsPhaseChecks.
Print Assumptions Inv_1568c_total_range.
Print Assumptions Inv_1568c_rank.
Print Assumptions Inv_15694_counter_range.
Print Assumptions Inv_15694_rank.
Print Assumptions rank_15694_at_15698.
