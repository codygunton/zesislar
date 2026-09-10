From Coq Require Import Arith.PeanoNat Lia.

Inductive WriteSuccessWithdrawalsPhase : Type :=
| WithdrawalsPrefix
| WithdrawalsMemcpy
| WithdrawalsIndexHandoff
| WithdrawalsIndexEncoder
| WithdrawalsValidatorHandoff
| WithdrawalsValidatorEncoder
| WithdrawalsOutputHandoff
| WithdrawalsAddressOutput
| WithdrawalsAmountHandoff
| WithdrawalsAmountEncoder
| WithdrawalsLoopTail.

Definition writeSuccessWithdrawalsPhaseStart
    (phase : WriteSuccessWithdrawalsPhase) : nat :=
  match phase with
  | WithdrawalsPrefix => 0
  | WithdrawalsMemcpy => 5
  | WithdrawalsIndexHandoff => 344
  | WithdrawalsIndexEncoder => 347
  | WithdrawalsValidatorHandoff => 362
  | WithdrawalsValidatorEncoder => 365
  | WithdrawalsOutputHandoff => 380
  | WithdrawalsAddressOutput => 384
  | WithdrawalsAmountHandoff => 389
  | WithdrawalsAmountEncoder => 392
  | WithdrawalsLoopTail => 407
  end.

Definition writeSuccessWithdrawalsPhaseLength
    (phase : WriteSuccessWithdrawalsPhase) : nat :=
  match phase with
  | WithdrawalsPrefix => 5
  | WithdrawalsMemcpy => 339
  | WithdrawalsIndexHandoff => 3
  | WithdrawalsIndexEncoder => 15
  | WithdrawalsValidatorHandoff => 3
  | WithdrawalsValidatorEncoder => 15
  | WithdrawalsOutputHandoff => 4
  | WithdrawalsAddressOutput => 5
  | WithdrawalsAmountHandoff => 3
  | WithdrawalsAmountEncoder => 15
  | WithdrawalsLoopTail => 3
  end.

Lemma writeSuccessWithdrawalsPositionPartition position :
  position < 410 ->
  exists phase localOffset,
    position = writeSuccessWithdrawalsPhaseStart phase + localOffset /\
    localOffset < writeSuccessWithdrawalsPhaseLength phase /\
    forall otherPhase otherOffset,
      position = writeSuccessWithdrawalsPhaseStart otherPhase + otherOffset ->
      otherOffset < writeSuccessWithdrawalsPhaseLength otherPhase ->
      otherPhase = phase /\ otherOffset = localOffset.
Proof.
  intros Hposition.
  destruct (Nat.lt_ge_cases position 5) as [H5|H5].
  - exists WithdrawalsPrefix, position. cbn. split; [lia |]. split; [lia |].
    intros phase offset Heq Hoffset. destruct phase; cbn in *; try lia.
    split; [reflexivity | lia].
  - destruct (Nat.lt_ge_cases position 344) as [H344|H344].
    + exists WithdrawalsMemcpy, (position - 5). cbn.
      split; [lia |]. split; [lia |].
      intros phase offset Heq Hoffset. destruct phase; cbn in *; try lia.
      split; [reflexivity | lia].
    + destruct (Nat.lt_ge_cases position 347) as [H347|H347].
      * exists WithdrawalsIndexHandoff, (position - 344). cbn.
        split; [lia |]. split; [lia |].
        intros phase offset Heq Hoffset. destruct phase; cbn in *; try lia.
        split; [reflexivity | lia].
      * destruct (Nat.lt_ge_cases position 362) as [H362|H362].
        -- exists WithdrawalsIndexEncoder, (position - 347). cbn.
           split; [lia |]. split; [lia |].
           intros phase offset Heq Hoffset. destruct phase; cbn in *; try lia.
           split; [reflexivity | lia].
        -- destruct (Nat.lt_ge_cases position 365) as [H365|H365].
           ++ exists WithdrawalsValidatorHandoff, (position - 362). cbn.
              split; [lia |]. split; [lia |].
              intros phase offset Heq Hoffset. destruct phase; cbn in *; try lia.
              split; [reflexivity | lia].
           ++ destruct (Nat.lt_ge_cases position 380) as [H380|H380].
              ** exists WithdrawalsValidatorEncoder, (position - 365). cbn.
                 split; [lia |]. split; [lia |].
                 intros phase offset Heq Hoffset. destruct phase; cbn in *;
                   try lia.
                 split; [reflexivity | lia].
              ** destruct (Nat.lt_ge_cases position 384) as [H384|H384].
                 --- exists WithdrawalsOutputHandoff, (position - 380). cbn.
                     split; [lia |]. split; [lia |].
                     intros phase offset Heq Hoffset. destruct phase; cbn in *;
                       try lia.
                     split; [reflexivity | lia].
                 --- destruct (Nat.lt_ge_cases position 389) as [H389|H389].
                     +++ exists WithdrawalsAddressOutput, (position - 384). cbn.
                         split; [lia |]. split; [lia |].
                         intros phase offset Heq Hoffset. destruct phase;
                           cbn in *; try lia.
                         split; [reflexivity | lia].
                     +++ destruct (Nat.lt_ge_cases position 392) as [H392|H392].
                         *** exists WithdrawalsAmountHandoff,
                               (position - 389). cbn.
                             split; [lia |]. split; [lia |].
                             intros phase offset Heq Hoffset. destruct phase;
                               cbn in *; try lia.
                             split; [reflexivity | lia].
                         *** destruct (Nat.lt_ge_cases position 407) as [H407|H407].
                             ---- exists WithdrawalsAmountEncoder,
                                    (position - 392). cbn.
                                  split; [lia |]. split; [lia |].
                                  intros phase offset Heq Hoffset.
                                  destruct phase; cbn in *; try lia.
                                  split; [reflexivity | lia].
                             ---- exists WithdrawalsLoopTail,
                                    (position - 407). cbn.
                                  split; [lia |]. split; [lia |].
                                  intros phase offset Heq Hoffset.
                                  destruct phase; cbn in *; try lia.
                                  split; [reflexivity | lia].
Qed.

Print Assumptions writeSuccessWithdrawalsPositionPartition.
