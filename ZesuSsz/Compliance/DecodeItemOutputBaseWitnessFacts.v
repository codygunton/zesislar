Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Compliance.DecodeItemRawOutputFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemOutputBaseOffset (args : DecodeItemArgs) :
  Z.of_nat 0 = decodeItemOutputPointer args + 0 - decodeItemOutputPointer args.
Proof. lia. Qed.

Lemma decodeItemFlagUpdatedBaseBound (storage : list byte) (first second : byte) (width : N) :
  length storage = 40%nat -> (width <= 8)%N ->
  (0 + N.to_nat width <= length (firstn 32 storage ++ first :: second :: skipn 34 storage))%nat.
Proof.
  intros Hlength Hwidth.
  rewrite app_length firstn_length. cbn [length].
  rewrite skipn_length Hlength. simpl. lia.
Qed.

#[export] Hint Extern 1
  (SimplAnd ((0 + N.to_nat ?width <=
    length (firstn 32 ?storage ++ ?first :: ?second :: skipn 34 ?storage))%nat) True) =>
  assert_fails (has_evar width);
  unfold SimplAnd; split;
  [intros _; apply decodeItemFlagUpdatedBaseBound; [eassumption | lia] | intros _; exact I]
  : typeclass_instances.

Print Assumptions decodeItemOutputBaseOffset.
Print Assumptions decodeItemFlagUpdatedBaseBound.

Lemma decodeItemOutputOffset8 (args : DecodeItemArgs) :
  Z.of_nat 8 = decodeItemOutputPointer args + 8 - decodeItemOutputPointer args.
Proof. lia. Qed.

Print Assumptions decodeItemOutputOffset8.

Lemma decodeItemOutputOffset16 (args : DecodeItemArgs) :
  Z.of_nat 16 =
    (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) `div` 1.
Proof. rewrite Z.div_1_r. lia. Qed.

Print Assumptions decodeItemOutputOffset16.

Lemma decodeItemOutputStorageExtent16 (base : Z) (storage : list byte) :
  length storage = 40%nat ->
  (Z.to_nat (base + 16 - base) + N.to_nat 8 <= length storage)%nat.
Proof.
  intros Hlength. replace (base + 16 - base) with 16 by lia.
  rewrite Hlength. cbn. lia.
Qed.

Lemma decodeItemOutputStorageExtent24 (base : Z) (storage : list byte) :
  length storage = 40%nat ->
  (Z.to_nat (base + 24 - base) + N.to_nat 8 <= length storage)%nat.
Proof.
  intros Hlength. replace (base + 24 - base) with 24 by lia.
  rewrite Hlength. cbn. lia.
Qed.

Lemma decodeItemOutputWord32Length (base : Z) (storage bytes : list byte) :
  length storage = 40%nat -> length bytes = 8%nat ->
  length (take (Z.to_nat (base + 32 - base)) storage ++ bytes ++
    drop (Z.to_nat (base + 32 - base) + N.to_nat 8) storage) = 40%nat.
Proof.
  intros Hstorage Hbytes. replace (base + 32 - base) with 32 by lia.
  rewrite !length_app length_take length_drop Hstorage Hbytes. cbn. lia.
Qed.

#[export] Hint Extern 1
  (SimplAnd ((Z.to_nat (?base + 16 - ?base) + N.to_nat 8 <= length ?storage)%nat) True) =>
  assert_fails (has_evar storage);
  match goal with Hlength : length ?before = 40%nat |- _ =>
    unfold SimplAnd; split;
    [intros _; apply decodeItemOutputStorageExtent16;
     first [eassumption | zesu_byte_array_lengths_if_enabled; rewrite Hlength; cbn; lia]
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd ((16 + N.to_nat 8 <= length ?storage)%nat) True) =>
  assert_fails (has_evar storage);
  match goal with Hlength : length ?before = 40%nat |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemOutputStorageExtent16 0);
     first [eassumption | zesu_byte_array_lengths_if_enabled; rewrite Hlength; cbn; lia]
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd ((Z.to_nat (?base + 24 - ?base) + N.to_nat 8 <= length ?storage)%nat) True) =>
  assert_fails (has_evar storage);
  match goal with Hlength : length ?before = 40%nat |- _ =>
    unfold SimplAnd; split;
    [intros _; apply decodeItemOutputStorageExtent24;
     first [eassumption | zesu_byte_array_lengths_if_enabled; rewrite Hlength; cbn; lia]
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd ((24 + N.to_nat 8 <= length ?storage)%nat) True) =>
  assert_fails (has_evar storage);
  match goal with Hlength : length ?before = 40%nat |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemOutputStorageExtent24 0);
     first [eassumption | zesu_byte_array_lengths_if_enabled; rewrite Hlength; cbn; lia]
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (length (take (Z.to_nat (?base + 32 - ?base)) ?storage ++
    ?b0 :: ?b1 :: ?b2 :: ?b3 :: ?b4 :: ?b5 :: ?b6 :: ?b7 ::
    drop (Z.to_nat (?base + 32 - ?base) + N.to_nat 8) ?storage) = 40%nat) True) =>
  assert_fails (has_evar storage);
  unfold SimplAnd; split;
  [intros _; apply (decodeItemOutputWord32Length base storage [b0; b1; b2; b3; b4; b5; b6; b7]);
   [eassumption | reflexivity]
  | intros _; exact I] : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (length (take 32 ?storage ++
    ?b0 :: ?b1 :: ?b2 :: ?b3 :: ?b4 :: ?b5 :: ?b6 :: ?b7 :: drop 40 ?storage) = 40%nat) True) =>
  assert_fails (has_evar storage);
  unfold SimplAnd; split;
  [intros _; apply (decodeItemOutputWord32Length 0 storage [b0; b1; b2; b3; b4; b5; b6; b7]);
   [eassumption | reflexivity]
  | intros _; exact I] : typeclass_instances.

Print Assumptions decodeItemOutputStorageExtent16.
Print Assumptions decodeItemOutputStorageExtent24.
Print Assumptions decodeItemOutputWord32Length.
