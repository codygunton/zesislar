Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import ZesuSsz.Compliance.BugPredicates.

(** The transaction witness contains 4 MiB of list bytes.  These lemmas
    read its fixed prefix and suffix without expanding those bytes. *)

Lemma tx_tail_read width k :
  zesuReadLeAt width transactionCountWitnessInput
    (length transactionCountWitnessPrefix +
      (length transactionCountWitnessBytes + k))%nat =
    zesuReadLeAt width transactionCountWitnessSuffix k.
Proof.
  unfold transactionCountWitnessInput.
  rewrite zesuReadLeAt_app_right by lia.
  replace (length transactionCountWitnessPrefix +
    (length transactionCountWitnessBytes + k) -
    length transactionCountWitnessPrefix)%nat with
    (length transactionCountWitnessBytes + k)%nat by lia.
  rewrite zesuReadLeAt_app_right by lia.
  replace (length transactionCountWitnessBytes + k -
    length transactionCountWitnessBytes)%nat with k by lia.
  reflexivity.
Qed.

Lemma tx_suffix_length : length transactionCountWitnessSuffix = 104%nat.
Proof.
  unfold transactionCountWitnessSuffix.
  repeat rewrite app_length.
  repeat rewrite repeat_length.
  reflexivity.
Qed.

Lemma tx_input_length : length transactionCountWitnessInput = 4195014%nat.
Proof.
  unfold transactionCountWitnessInput.
  rewrite app_length.
  rewrite app_length.
  rewrite transactionCountWitnessPrefixLength,
    transactionCountWitnessLength, tx_suffix_length.
  apply Nat.eqb_eq. vm_compute. reflexivity.
Qed.

Lemma tx_top_read :
  zesuReadU32At transactionCountWitnessInput 0 = Some 1048847.
Proof.
  unfold transactionCountWitnessInput, zesuReadU32At.
  rewrite zesuReadLeAt_app_left
    by (rewrite transactionCountWitnessPrefixLength; lia).
  reflexivity.
Qed.

Lemma tx_payload :
  zesuBugPayload transactionCountWitnessInput = transactionCountWitnessInput.
Proof.
  unfold zesuBugPayload.
  rewrite tx_top_read, tx_input_length.
  replace (Nat.eqb 4195014 (4 + Z.to_nat 1048847)) with false
    by (vm_compute; reflexivity).
  reflexivity.
Qed.

Ltac tx_prefix :=
  unfold zesuReadU32At, zesuReadU64At;
  unfold transactionCountWitnessInput;
  rewrite zesuReadLeAt_app_left
    by (rewrite transactionCountWitnessPrefixLength; lia);
  reflexivity.

Ltac tx_tail k :=
  unfold zesuReadU32At, zesuReadU64At;
  match goal with
  | |- zesuReadLeAt _ transactionCountWitnessInput ?offset = _ =>
      replace offset with
        (length transactionCountWitnessPrefix +
          (length transactionCountWitnessBytes + k))%nat
        by (rewrite transactionCountWitnessPrefixLength,
                    transactionCountWitnessLength;
            apply Nat.eqb_eq; vm_compute; reflexivity)
  end;
  rewrite tx_tail_read;
  reflexivity.

Lemma tx_read_2 : zesuReadU32At transactionCountWitnessInput 2 = Some 16.
Proof. tx_prefix. Qed.
Lemma tx_read_6 : zesuReadU32At transactionCountWitnessInput 6 = Some 4194960.
Proof. tx_prefix. Qed.
Lemma tx_read_10 : zesuReadU32At transactionCountWitnessInput 10 = Some 4194972.
Proof. tx_prefix. Qed.
Lemma tx_read_14 : zesuReadU32At transactionCountWitnessInput 14 = Some 4195012.
Proof. tx_prefix. Qed.
Lemma tx_read_18 : zesuReadU32At transactionCountWitnessInput 18 = Some 44.
Proof. tx_prefix. Qed.
Lemma tx_read_22 : zesuReadU32At transactionCountWitnessInput 22 = Some 4194892.
Proof. tx_prefix. Qed.
Lemma tx_read_58 : zesuReadU32At transactionCountWitnessInput 58 = Some 4194924.
Proof. tx_prefix. Qed.
Lemma tx_read_466 : zesuReadU64At transactionCountWitnessInput 466 = Some 0.
Proof. tx_prefix. Qed.
Lemma tx_read_490 : zesuReadU64At transactionCountWitnessInput 490 = Some 0.
Proof. tx_prefix. Qed.
Lemma tx_read_498 : zesuReadU32At transactionCountWitnessInput 498 = Some 540.
Proof. tx_prefix. Qed.
Lemma tx_read_566 : zesuReadU32At transactionCountWitnessInput 566 = Some 540.
Proof. tx_prefix. Qed.
Lemma tx_read_570 : zesuReadU32At transactionCountWitnessInput 570 = Some 4194848.
Proof. tx_prefix. Qed.

Lemma tx_read_request : zesuReadU32At transactionCountWitnessInput 4194942 = Some 20.
Proof. tx_tail 32%nat. Qed.
Lemma tx_read_chain : zesuReadU64At transactionCountWitnessInput 4194974 = Some 1.
Proof. tx_tail 64%nat. Qed.
Lemma tx_read_chain_expr :
  zesuReadU64At transactionCountWitnessInput
    (2 + Z.to_nat 4194972)%nat = Some 1.
Proof.
  replace (2 + Z.to_nat 4194972)%nat with 4194974%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  exact tx_read_chain.
Qed.
Lemma tx_read_chain_offset : zesuReadU32At transactionCountWitnessInput 4194982 = Some 12.
Proof. tx_tail 72%nat. Qed.
Lemma tx_read_chain_offset_expr :
  zesuReadU32At transactionCountWitnessInput
    (2 + Z.to_nat 4194972 + 8)%nat = Some 12.
Proof.
  replace (2 + Z.to_nat 4194972 + 8)%nat with 4194982%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  exact tx_read_chain_offset.
Qed.
Lemma tx_read_active_offset : zesuReadU32At transactionCountWitnessInput 4194986 = Some 4.
Proof. tx_tail 76%nat. Qed.
Lemma tx_read_block_offset : zesuReadU32At transactionCountWitnessInput 4194990 = Some 8.
Proof. tx_tail 80%nat. Qed.
Lemma tx_read_timestamp_offset : zesuReadU32At transactionCountWitnessInput 4194994 = Some 16.
Proof. tx_tail 84%nat. Qed.
Lemma tx_read_block_activation : zesuReadU64At transactionCountWitnessInput 4194998 = Some 0.
Proof. tx_tail 88%nat. Qed.
Lemma tx_read_timestamp_activation : zesuReadU64At transactionCountWitnessInput 4195006 = Some 0.
Proof. tx_tail 96%nat. Qed.
