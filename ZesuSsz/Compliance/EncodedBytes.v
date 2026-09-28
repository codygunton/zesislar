Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncodeLeByteValues width value :
  Forall writeSuccessByte (writeSuccessEncodeLe width value).
Proof.
  revert value. induction width; intros value; simpl; constructor.
  - unfold writeSuccessByte. apply Z.mod_pos_bound. lia.
  - apply IHwidth.
Qed.

Lemma writeSuccessFixedByteValues width bytes :
  writeSuccessBytesValid width bytes -> Forall writeSuccessByte bytes.
Proof. intros [_ Hbytes]. exact Hbytes. Qed.
Lemma writeSuccessVariableByteValues bytes :
  writeSuccessVariableBytesValid bytes -> Forall writeSuccessByte bytes.
Proof. intros [_ Hbytes]. exact Hbytes. Qed.

Lemma writeSuccessEncodeBytesByteValues bytes :
  writeSuccessVariableBytesValid bytes ->
  Forall writeSuccessByte (writeSuccessEncodeBytes bytes).
Proof.
  intros [_ Hbytes]. unfold writeSuccessEncodeBytes.
  apply Forall_app. split; last exact Hbytes.
  apply writeSuccessEncodeLeByteValues.
Qed.

Lemma writeSuccessEncodeListByteValues {A} (valid : A -> Prop) encode items :
  (forall item, valid item -> Forall writeSuccessByte (encode item)) ->
  writeSuccessListValid valid items ->
  Forall writeSuccessByte (writeSuccessEncodeList encode items).
Proof.
  intros Hencode [_ Hitems]. unfold writeSuccessEncodeList.
  apply Forall_app. split; first apply writeSuccessEncodeLeByteValues.
  induction Hitems; simpl; first constructor.
  apply Forall_app. split; first apply Hencode; assumption.
Qed.

Lemma writeSuccessEncodeOptionalByteValues encode value :
  (forall item, Forall writeSuccessByte (encode item)) ->
  Forall writeSuccessByte (writeSuccessEncodeOptional encode value).
Proof.
  intros Hencode. destruct value; simpl; constructor;
    try (unfold writeSuccessByte; lia); auto.
Qed.

Lemma writeSuccessEncodeOptionalBytesByteValues width value :
  writeSuccessOptionalBytesValid width value ->
  Forall writeSuccessByte (writeSuccessEncodeOptionalBytes value).
Proof.
  destruct value; simpl; intros Hvalid; constructor;
    try (unfold writeSuccessByte; lia).
  - exact (proj2 Hvalid).
  - constructor.
Qed.

Local Hint Extern 1 (Forall writeSuccessByte (writeSuccessEncodeU8 _)) =>
  apply writeSuccessEncodeLeByteValues : encoded_bytes.
Local Hint Extern 1 (Forall writeSuccessByte (writeSuccessEncodeU64 _)) =>
  apply writeSuccessEncodeLeByteValues : encoded_bytes.
Local Hint Extern 1 (Forall writeSuccessByte (writeSuccessEncodeU128 _)) =>
  apply writeSuccessEncodeLeByteValues : encoded_bytes.
Local Hint Extern 1 (Forall writeSuccessByte (writeSuccessEncodeU256 _)) =>
  apply writeSuccessEncodeLeByteValues : encoded_bytes.

Local Hint Resolve writeSuccessEncodeLeByteValues writeSuccessFixedByteValues
  writeSuccessVariableByteValues writeSuccessEncodeBytesByteValues
  writeSuccessEncodeListByteValues writeSuccessEncodeOptionalByteValues
  writeSuccessEncodeOptionalBytesByteValues : encoded_bytes.

Lemma writeSuccessEncodeAccessByteValues entry :
  writeSuccessAccessEntryValid entry ->
  Forall writeSuccessByte (writeSuccessEncodeAccessEntry entry).
Proof.
  intros [Haddress Hkeys]. unfold writeSuccessEncodeAccessEntry.
  apply Forall_app. split; eauto 8 with encoded_bytes.
Qed.

Lemma writeSuccessEncodeAuthorizationByteValues authorization :
  writeSuccessAuthorizationValid authorization ->
  Forall writeSuccessByte (writeSuccessEncodeAuthorization authorization).
Proof.
  unfold writeSuccessAuthorizationValid, writeSuccessEncodeAuthorization.
  intros Hvalid. repeat match type of Hvalid with _ /\ _ => destruct Hvalid as [? Hvalid] end.
  repeat rewrite Forall_app. repeat split;
    eauto 6 with encoded_bytes.
Qed.
Local Hint Resolve writeSuccessEncodeAccessByteValues
  writeSuccessEncodeAuthorizationByteValues : encoded_bytes.

Lemma writeSuccessEncodeTransactionByteValues transaction :
  writeSuccessTransactionObservationValid transaction ->
  Forall writeSuccessByte (writeSuccessEncodeTransaction transaction).
Proof.
  unfold writeSuccessTransactionObservationValid, writeSuccessEncodeTransaction.
  intros Hvalid. repeat match type of Hvalid with _ /\ _ => destruct Hvalid as [? Hvalid] end.
  repeat rewrite Forall_app. repeat split;
    eauto 12 with encoded_bytes.
Qed.

Lemma writeSuccessEncodeWithdrawalByteValues withdrawal :
  writeSuccessWithdrawalObservationValid withdrawal ->
  Forall writeSuccessByte (writeSuccessEncodeWithdrawal withdrawal).
Proof.
  unfold writeSuccessWithdrawalObservationValid, writeSuccessEncodeWithdrawal.
  intros Hvalid. repeat match type of Hvalid with _ /\ _ => destruct Hvalid as [? Hvalid] end.
  repeat rewrite Forall_app. repeat split;
    eauto 6 with encoded_bytes.
Qed.
Local Hint Resolve writeSuccessEncodeTransactionByteValues
  writeSuccessEncodeWithdrawalByteValues : encoded_bytes.

Lemma writeSuccessEncodeObservationByteValues observation :
  writeSuccessObservationValid observation ->
  Forall writeSuccessByte (writeSuccessEncodeObservation observation).
Proof.
  unfold writeSuccessObservationValid, writeSuccessEncodeObservation.
  intros Hvalid. repeat match type of Hvalid with _ /\ _ => destruct Hvalid as [? Hvalid] end.
  repeat rewrite Forall_app. repeat split;
    eauto 12 with encoded_bytes.
  all: try (repeat constructor; unfold writeSuccessByte; lia).
  assert (HforkValid :
    match observationForkName observation with
    | Some name => writeSuccessVariableBytesValid name
    | None => True
    end) by assumption.
  destruct (observationForkName observation) as [name|].
  - change (Forall writeSuccessByte (1 :: writeSuccessEncodeBytes name)).
    constructor.
    + unfold writeSuccessByte. lia.
    + apply writeSuccessEncodeBytesByteValues. exact HforkValid.
  - repeat constructor; unfold writeSuccessByte; lia.
Qed.
Print Assumptions writeSuccessEncodeObservationByteValues.
