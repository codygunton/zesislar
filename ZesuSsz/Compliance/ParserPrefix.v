Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List Bool.Bool Lia ZArith.ZArith.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Compliance.ObservationBridge.
Import ListNotations.

Definition writeSuccessParserStable {A} (parse : WriteSuccessParser A) : Prop :=
  forall input value rest suffix,
    parse input = Some (value, rest) ->
    parse (input ++ suffix) = Some (value, rest ++ suffix).

Lemma writeSuccessParserStable_return {A} (value : A) :
  writeSuccessParserStable (fun input => Some (value, input)).
Proof. intros input result rest suffix Hparse. inversion Hparse. reflexivity. Qed.

Lemma writeSuccessParserStable_none {A} : writeSuccessParserStable (fun _ => @None (A * ByteString)).
Proof. intros input value rest suffix Hparse. discriminate. Qed.

Lemma writeSuccessParserStable_bind {A B} (parse : WriteSuccessParser A)
    (next : A -> WriteSuccessParser B) :
  writeSuccessParserStable parse ->
  (forall value, writeSuccessParserStable (next value)) ->
  writeSuccessParserStable (fun input => writeSuccessParserBind (parse input) next).
Proof.
  intros Hparse Hnext input value rest suffix Hresult.
  destruct (parse input) as [[parsed remaining]|] eqn:Hfirst; simpl in Hresult;
    last discriminate.
  rewrite (Hparse _ _ _ suffix Hfirst). simpl.
  exact (Hnext _ _ _ _ suffix Hresult).
Qed.

Lemma writeSuccessParserStable_fixed width : writeSuccessParserStable (writeSuccessParseFixed width).
Proof.
  intros input value rest suffix Hparse. unfold writeSuccessParseFixed in *.
  destruct (Nat.leb width (length input)) eqn:Hwidth; last discriminate.
  apply Nat.leb_le in Hwidth.
  assert (Hwidth' : Nat.leb width (length (input ++ suffix)) = true).
  { apply Nat.leb_le. rewrite app_length. lia. }
  rewrite Hwidth'.
  rewrite firstn_app, (proj2 (Nat.sub_0_le _ _) Hwidth). simpl.
  rewrite app_nil_r.
  destruct (forallb writeSuccessByteb (firstn width input)); last discriminate.
  inversion Hparse. subst. rewrite skipn_app.
  rewrite (proj2 (Nat.sub_0_le _ _) Hwidth). reflexivity.
Qed.

Lemma writeSuccessParserStable_integer width : writeSuccessParserStable (writeSuccessParseInteger width).
Proof.
  unfold writeSuccessParseInteger. apply writeSuccessParserStable_bind.
  - apply writeSuccessParserStable_fixed.
  - intros. apply writeSuccessParserStable_return.
Qed.

Lemma writeSuccessParserStable_bytes : writeSuccessParserStable writeSuccessParseBytes.
Proof.
  intros input value rest suffix Hparse. unfold writeSuccessParseBytes in *.
  destruct (writeSuccessParseInteger 8 input) as [[declared remaining]|] eqn:Hfirst;
    simpl in Hparse; last discriminate.
  rewrite (writeSuccessParserStable_integer 8 _ _ _ suffix Hfirst). simpl.
  destruct (declared <=? Z.of_nat (length remaining))%Z eqn:Hfits; last discriminate.
  apply Z.leb_le in Hfits.
  assert (Hfits' : (declared <=? Z.of_nat (length (remaining ++ suffix)))%Z = true).
  { apply Z.leb_le. rewrite app_length. lia. }
  rewrite Hfits'. exact (writeSuccessParserStable_fixed _ _ _ _ suffix Hparse).
Qed.

Lemma writeSuccessParserStable_items {A} (parse : WriteSuccessParser A) count :
  writeSuccessParserStable parse -> writeSuccessParserStable (writeSuccessParseItems parse count).
Proof.
  intros Hparse. induction count; simpl.
  - apply writeSuccessParserStable_return.
  - apply writeSuccessParserStable_bind; first exact Hparse.
    intros value. apply writeSuccessParserStable_bind; first exact IHcount.
    intros values. apply writeSuccessParserStable_return.
Qed.

Lemma writeSuccessParserStable_list {A} (parse : WriteSuccessParser A) :
  writeSuccessParserStable parse -> writeSuccessParserStable (writeSuccessParseList parse).
Proof.
  intros Hstable input value rest suffix Hparse. unfold writeSuccessParseList in *.
  destruct (writeSuccessParseInteger 8 input) as [[declared remaining]|] eqn:Hfirst;
    simpl in Hparse; last discriminate.
  rewrite (writeSuccessParserStable_integer 8 _ _ _ suffix Hfirst). simpl.
  destruct (declared <=? Z.of_nat (length remaining))%Z eqn:Hfits; last discriminate.
  apply Z.leb_le in Hfits.
  assert (Hfits' : (declared <=? Z.of_nat (length (remaining ++ suffix)))%Z = true).
  { apply Z.leb_le. rewrite app_length. lia. }
  rewrite Hfits'. exact (writeSuccessParserStable_items _ _ Hstable _ _ _ suffix Hparse).
Qed.

Lemma writeSuccessParserStable_optional_integer width :
  writeSuccessParserStable (writeSuccessParseOptionalInteger width).
Proof.
  unfold writeSuccessParseOptionalInteger. apply writeSuccessParserStable_bind.
  - apply writeSuccessParserStable_integer.
  - intros [|[positive|positive|]|positive]; simpl;
      try apply writeSuccessParserStable_return; try apply writeSuccessParserStable_none.
    apply writeSuccessParserStable_bind; first apply writeSuccessParserStable_integer.
    intros. apply writeSuccessParserStable_return.
Qed.

Lemma writeSuccessParserStable_optional_fixed width :
  writeSuccessParserStable (writeSuccessParseOptionalFixed width).
Proof.
  unfold writeSuccessParseOptionalFixed. apply writeSuccessParserStable_bind.
  - apply writeSuccessParserStable_integer.
  - intros [|[positive|positive|]|positive]; simpl;
      try apply writeSuccessParserStable_return; try apply writeSuccessParserStable_none.
    apply writeSuccessParserStable_bind; first apply writeSuccessParserStable_fixed.
    intros. apply writeSuccessParserStable_return.
Qed.

Lemma writeSuccessParserStable_optional_bytes : writeSuccessParserStable writeSuccessParseOptionalBytes.
Proof.
  unfold writeSuccessParseOptionalBytes. apply writeSuccessParserStable_bind.
  - apply writeSuccessParserStable_integer.
  - intros [|[positive|positive|]|positive]; simpl;
      try apply writeSuccessParserStable_return; try apply writeSuccessParserStable_none.
    apply writeSuccessParserStable_bind; first apply writeSuccessParserStable_bytes.
    intros. apply writeSuccessParserStable_return.
Qed.

Local Hint Resolve writeSuccessParserStable_return writeSuccessParserStable_none writeSuccessParserStable_bind
  writeSuccessParserStable_fixed writeSuccessParserStable_integer writeSuccessParserStable_bytes writeSuccessParserStable_list
  writeSuccessParserStable_optional_integer writeSuccessParserStable_optional_fixed
  writeSuccessParserStable_optional_bytes : parser_stable.

Lemma writeSuccessParserStable_access : writeSuccessParserStable writeSuccessParseAccessEntry.
Proof. unfold writeSuccessParseAccessEntry. eauto 12 with parser_stable. Qed.
Lemma writeSuccessParserStable_authorization : writeSuccessParserStable writeSuccessParseAuthorization.
Proof. unfold writeSuccessParseAuthorization. eauto 20 with parser_stable. Qed.
Local Hint Resolve writeSuccessParserStable_access writeSuccessParserStable_authorization : parser_stable.
Lemma writeSuccessParserStable_transaction : writeSuccessParserStable writeSuccessParseTransaction.
Proof. unfold writeSuccessParseTransaction. eauto 50 with parser_stable. Qed.
Lemma writeSuccessParserStable_withdrawal : writeSuccessParserStable writeSuccessParseWithdrawal.
Proof. unfold writeSuccessParseWithdrawal. eauto 16 with parser_stable. Qed.
Local Hint Resolve writeSuccessParserStable_transaction writeSuccessParserStable_withdrawal : parser_stable.

Lemma writeSuccessParserStable_observation : writeSuccessParserStable writeSuccessParseObservation.
Proof.
  unfold writeSuccessParseObservation. apply writeSuccessParserStable_bind; first apply writeSuccessParserStable_fixed.
  intros magic. destruct (list_eq_dec Z.eq_dec magic [90; 83; 83; 90; 1; 1]);
    eauto 100 with parser_stable.
Qed.

Lemma writeSuccessDecodeObservationPrefix observation observed bytes suffix :
  writeSuccessObservationValid observation ->
  bytes ++ suffix = writeSuccessEncodeObservation observation ->
  writeSuccessDecodeObservation bytes = Some observed ->
  observed = observation /\ bytes = writeSuccessEncodeObservation observation.
Proof.
  intros Hvalid Hbytes Hdecode. unfold writeSuccessDecodeObservation in Hdecode.
  destruct (writeSuccessParseObservation bytes) as [[parsed rest]|] eqn:Hparse;
    last discriminate.
  destruct rest; last discriminate. inversion Hdecode. subst parsed.
  pose proof (writeSuccessParserStable_observation bytes observed [] suffix Hparse) as Hextended.
  simpl in Hextended. rewrite Hbytes in Hextended.
  pose proof (writeSuccessParseObservationRoundTrip observation [] Hvalid) as Hfull.
  rewrite app_nil_r in Hfull. rewrite Hfull in Hextended.
  inversion Hextended. subst suffix observation. rewrite app_nil_r in Hbytes. auto.
Qed.
Print Assumptions writeSuccessDecodeObservationPrefix.

Lemma writeSuccessDecodeObservationSuffix observation observed suffix :
  writeSuccessObservationValid observation ->
  writeSuccessDecodeObservation (writeSuccessEncodeObservation observation ++ suffix) =
    Some observed ->
  observed = observation /\ suffix = [].
Proof.
  intros Hvalid Hdecode. unfold writeSuccessDecodeObservation in Hdecode.
  rewrite (writeSuccessParseObservationRoundTrip observation suffix Hvalid) in Hdecode.
  destruct suffix; inversion Hdecode; subst observed; auto.
Qed.
Print Assumptions writeSuccessDecodeObservationSuffix.
