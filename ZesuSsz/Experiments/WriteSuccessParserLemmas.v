From Coq Require Import Bool.Bool Lia Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncodeLeLength width value :
  length (writeSuccessEncodeLe width value) = width.
Proof.
  revert value. induction width; intros value; simpl; auto.
Qed.

Lemma writeSuccessEncodeLeBytes width value :
  0 <= value ->
  Forall writeSuccessByte (writeSuccessEncodeLe width value).
Proof.
  revert value. induction width; intros value Hvalue; simpl; constructor.
  - unfold writeSuccessByte. split.
    + apply Z.mod_pos_bound. lia.
    + apply Z.mod_pos_bound. lia.
  - apply IHwidth. apply Z.div_pos; lia.
Qed.

Lemma writeSuccessDecodeLeEncodeLe width value :
  0 <= value < 2 ^ Z.of_nat (8 * width) ->
  writeSuccessDecodeLe (writeSuccessEncodeLe width value) = value.
Proof.
  revert value. induction width as [|width IH]; intros value Hvalue.
  - simpl in *. lia.
  - simpl.
    rewrite IH.
    + assert (H256 : 256 <> 0) by lia.
      pose proof (Z.div_mod value 256 H256). lia.
    + split.
      * apply Z.div_pos; lia.
      * replace (8 * S width)%nat with (8 * width + 8)%nat in Hvalue by lia.
        rewrite Nat2Z.inj_add in Hvalue.
        rewrite Z.pow_add_r in Hvalue; [|lia|lia].
        cbn in Hvalue.
        apply Z.div_lt_upper_bound; lia.
Qed.

Lemma writeSuccessBytebTrue byte :
  writeSuccessByte byte -> writeSuccessByteb byte = true.
Proof.
  intros [Hlow Hhigh]. unfold writeSuccessByteb.
  apply andb_true_iff. split.
  - apply Z.leb_le. exact Hlow.
  - apply Z.ltb_lt. exact Hhigh.
Qed.

Lemma writeSuccessParseFixedApp width bytes tail :
  length bytes = width ->
  Forall writeSuccessByte bytes ->
  writeSuccessParseFixed width (bytes ++ tail) = Some (bytes, tail).
Proof.
  intros Hlength Hbytes. unfold writeSuccessParseFixed.
  assert (Hfits : Nat.leb width (length (bytes ++ tail)) = true).
  { apply Nat.leb_le. rewrite app_length, Hlength. lia. }
  rewrite Hfits.
  assert (Hfirst : firstn width bytes = bytes).
  { apply firstn_all2. lia. }
  rewrite firstn_app, Hfirst, Hlength, Nat.sub_diag, firstn_O, app_nil_r.
  assert (Hforall : forall x, In x bytes -> writeSuccessByteb x = true).
  { intros x Hx. apply writeSuccessBytebTrue.
    eapply Forall_forall; eassumption. }
  assert (Hbytesb : forallb writeSuccessByteb bytes = true).
  { apply forallb_forall. exact Hforall. }
  rewrite Hbytesb.
  assert (Hskip : skipn width bytes = []).
  { apply skipn_all2. lia. }
  rewrite skipn_app, Hskip, Hlength, Nat.sub_diag, skipn_O, app_nil_l.
  reflexivity.
Qed.

Lemma writeSuccessParseIntegerRoundTrip width value tail :
  writeSuccessUnsignedValid width value ->
  writeSuccessParseInteger width
    (writeSuccessEncodeLe width value ++ tail) = Some (value, tail).
Proof.
  intros Hvalid. unfold writeSuccessParseInteger.
  rewrite writeSuccessParseFixedApp.
  - cbn [writeSuccessParserBind].
    rewrite writeSuccessDecodeLeEncodeLe; [reflexivity | exact Hvalid].
  - apply writeSuccessEncodeLeLength.
  - apply writeSuccessEncodeLeBytes. exact (proj1 Hvalid).
Qed.

Lemma writeSuccessParseBytesRoundTrip bytes tail :
  writeSuccessVariableBytesValid bytes ->
  writeSuccessParseBytes (writeSuccessEncodeBytes bytes ++ tail) =
    Some (bytes, tail).
Proof.
  intros [Hlength Hbytes]. unfold writeSuccessEncodeBytes, writeSuccessParseBytes.
  rewrite <- app_assoc, writeSuccessParseIntegerRoundTrip.
  2: { unfold writeSuccessUnsignedValid. cbn. split; [lia | exact Hlength]. }
  cbn [writeSuccessParserBind].
  assert (Hfits : (Z.of_nat (length bytes) <=?
      Z.of_nat (length (bytes ++ tail))) = true).
  { apply Z.leb_le. rewrite app_length. lia. }
  rewrite Hfits.
  rewrite Nat2Z.id.
  apply writeSuccessParseFixedApp; [reflexivity | exact Hbytes].
Qed.

Lemma writeSuccessParseItemsRoundTrip {A}
    (parse : WriteSuccessParser A) (encode : A -> ByteString) :
  (forall item tail, parse (encode item ++ tail) = Some (item, tail)) ->
  forall items tail,
    writeSuccessParseItems parse (length items)
      (concat (map encode items) ++ tail) = Some (items, tail).
Proof.
  intros Hitem items. induction items as [|item items IH]; intros tail; simpl.
  - reflexivity.
  - rewrite <- app_assoc, Hitem. cbn [writeSuccessParserBind]. rewrite IH.
    reflexivity.
Qed.

Lemma writeSuccessParseListRoundTrip {A}
    (parse : WriteSuccessParser A) (encode : A -> ByteString) :
  (forall item tail, parse (encode item ++ tail) = Some (item, tail)) ->
  forall items tail,
    writeSuccessLengthValid items ->
    (length items <= length (concat (map encode items)))%nat ->
    writeSuccessParseList parse
      (writeSuccessEncodeList encode items ++ tail) = Some (items, tail).
Proof.
  intros Hitem items tail Hlength Hsize.
  unfold writeSuccessEncodeList, writeSuccessParseList.
  rewrite <- app_assoc, writeSuccessParseIntegerRoundTrip.
  2: { unfold writeSuccessUnsignedValid. cbn. split; [lia |].
       exact Hlength. }
  cbn [writeSuccessParserBind].
  assert (Hfits : (Z.of_nat (length items) <=?
      Z.of_nat (length (concat (map encode items) ++ tail))) = true).
  { apply Z.leb_le. rewrite app_length. lia. }
  rewrite Hfits.
  rewrite Nat2Z.id.
  apply writeSuccessParseItemsRoundTrip. exact Hitem.
Qed.

Lemma writeSuccessParseOptionalIntegerNone width tail :
  writeSuccessParseOptionalInteger width (0 :: tail) = Some (None, tail).
Proof. reflexivity. Qed.

Lemma writeSuccessParseOptionalIntegerSome width value tail :
  writeSuccessUnsignedValid width value ->
  writeSuccessParseOptionalInteger width
    (1 :: writeSuccessEncodeLe width value ++ tail) = Some (Some value, tail).
Proof.
  intros Hvalid.
  unfold writeSuccessParseOptionalInteger.
  replace (1 :: writeSuccessEncodeLe width value ++ tail) with
    (writeSuccessEncodeLe 1 1 ++
      (writeSuccessEncodeLe width value ++ tail)) by reflexivity.
  rewrite writeSuccessParseIntegerRoundTrip.
  2: { unfold writeSuccessUnsignedValid. cbn. lia. }
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseIntegerRoundTrip; [reflexivity | exact Hvalid].
Qed.

Lemma writeSuccessParseOptionalIntegerBadTag width tag tail :
  writeSuccessByte tag ->
  tag <> 0 -> tag <> 1 ->
  writeSuccessParseOptionalInteger width (tag :: tail) = None.
Proof.
  intros Hbyte Hzero Hone.
  unfold writeSuccessParseOptionalInteger, writeSuccessParseInteger.
  rewrite (writeSuccessParseFixedApp 1 [tag] tail).
  - cbn [writeSuccessParserBind writeSuccessDecodeLe].
    destruct tag as [|positive|positive].
    + contradiction.
    + destruct positive; [reflexivity | reflexivity | contradiction].
    + reflexivity.
  - reflexivity.
  - constructor; [exact Hbyte | constructor].
Qed.

Lemma writeSuccessParseOptionalFixedNone width tail :
  writeSuccessParseOptionalFixed width (0 :: tail) = Some (None, tail).
Proof. reflexivity. Qed.

Lemma writeSuccessParseOptionalFixedSome width bytes tail :
  writeSuccessBytesValid width bytes ->
  writeSuccessParseOptionalFixed width (1 :: bytes ++ tail) =
    Some (Some bytes, tail).
Proof.
  intros [Hlength Hbytes].
  unfold writeSuccessParseOptionalFixed.
  replace (1 :: bytes ++ tail) with
    (writeSuccessEncodeLe 1 1 ++ (bytes ++ tail)) by reflexivity.
  rewrite writeSuccessParseIntegerRoundTrip.
  2: { unfold writeSuccessUnsignedValid. cbn. lia. }
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseFixedApp; auto.
Qed.

Lemma writeSuccessParseOptionalBytesNone tail :
  writeSuccessParseOptionalBytes (0 :: tail) = Some (None, tail).
Proof. reflexivity. Qed.

Lemma writeSuccessParseOptionalBytesSome bytes tail :
  writeSuccessVariableBytesValid bytes ->
  writeSuccessParseOptionalBytes
    (1 :: writeSuccessEncodeBytes bytes ++ tail) = Some (Some bytes, tail).
Proof.
  intros Hvalid. unfold writeSuccessParseOptionalBytes.
  replace (1 :: writeSuccessEncodeBytes bytes ++ tail) with
    (writeSuccessEncodeLe 1 1 ++
      (writeSuccessEncodeBytes bytes ++ tail)) by reflexivity.
  rewrite writeSuccessParseIntegerRoundTrip.
  2: { unfold writeSuccessUnsignedValid. cbn. lia. }
  cbn [writeSuccessParserBind].
  rewrite writeSuccessParseBytesRoundTrip; auto.
Qed.

Print Assumptions writeSuccessParseIntegerRoundTrip.
Print Assumptions writeSuccessParseBytesRoundTrip.
Print Assumptions writeSuccessParseListRoundTrip.
Print Assumptions writeSuccessParseOptionalFixedSome.
Print Assumptions writeSuccessParseOptionalBytesSome.
