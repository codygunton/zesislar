Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.ResultImage.
From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.


Lemma decodeItemRawOutputStatus (before pointerBytes lengthBytes : list byte) :
  length before = 40%nat -> length pointerBytes = 8%nat -> length lengthBytes = 8%nat ->
  fieldImage (pointerBytes ++ lengthBytes ++
    skipn 16 (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before))
    32 [Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros Hbefore Hp Hl index Hindex.
  rewrite nth_error_app2; last (rewrite ?Hp ?Hl; lia).
  rewrite nth_error_app2; last (rewrite ?Hp ?Hl; lia).
  rewrite nth_error_skipn_offset.
  rewrite nth_error_app2; last (rewrite firstn_length Hbefore ?Hp ?Hl; lia).
  replace (16 + (32 + index - length pointerBytes - length lengthBytes) - length (firstn 32 before))%nat
    with index by (rewrite firstn_length Hbefore ?Hp ?Hl; lia).
  rewrite nth_error_app1; last (cbn in *; lia). reflexivity.
Qed.

Lemma decodeItemRawOutputPad17 (before pointerBytes lengthBytes : list byte) :
  length before = 40%nat -> length pointerBytes = 8%nat -> length lengthBytes = 8%nat ->
  preservedImage before (pointerBytes ++ lengthBytes ++
    skipn 16 (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before)) 17 7.
Proof.
  intros Hbefore Hp Hl index Hindex.
  rewrite nth_error_app2; last (rewrite ?Hp ?Hl; lia).
  rewrite nth_error_app2; last (rewrite ?Hp ?Hl; lia).
  rewrite nth_error_skipn_offset.
  rewrite nth_error_app1; last (rewrite firstn_length Hbefore ?Hp ?Hl; lia).
  rewrite nth_error_firstn_inside; last (rewrite Hp Hl; lia).
  f_equal. rewrite Hp Hl. lia.
Qed.

Lemma decodeItemRawOutputPad34 (before pointerBytes lengthBytes : list byte) :
  length before = 40%nat -> length pointerBytes = 8%nat -> length lengthBytes = 8%nat ->
  preservedImage before (pointerBytes ++ lengthBytes ++
    skipn 16 (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before)) 34 6.
Proof.
  intros Hbefore Hp Hl index Hindex.
  rewrite nth_error_app2; last (rewrite ?Hp ?Hl; lia).
  rewrite nth_error_app2; last (rewrite ?Hp ?Hl; lia).
  rewrite nth_error_skipn_offset.
  rewrite nth_error_app2; last (rewrite firstn_length Hbefore ?Hp ?Hl; lia).
  rewrite nth_error_app2; last (cbn; rewrite firstn_length Hbefore ?Hp ?Hl; lia).
  rewrite nth_error_skipn_offset. f_equal.
  rewrite firstn_length Hbefore Hp Hl. cbn. lia.
Qed.

Lemma decodeItemRawOutputExtent (before : list byte) (first second : byte) :
  length before = 40%nat ->
  (16 + length (skipn (N.to_nat 8) (skipn (N.to_nat 8)
    (firstn 32 before ++ first :: second :: skipn (32 + N.to_nat 2) before))) = 40)%nat.
Proof.
  intros Hlength. rewrite !skipn_length !app_length !firstn_length Hlength.
  cbn. rewrite !length_drop Hlength. cbn [N.to_nat]. lia.
Qed.

Lemma decodeItemRawInputPointer args :
  0 <= decodeItemInputPointer args -> 0 <= decodeItemInputLength args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = decodeItemInputPointer args + 0.
Proof.
  intros Hp Hl Hnowrap.
  assert (Hbounds : 0 <= decodeItemInputPointer args < bv_modulus 64).
  { unfold word64Modulus in Hnowrap. change (0 <= decodeItemInputPointer args < 2^64). lia. }
  rewrite (Z_to_bv_small 64 _ Hbounds). lia.
Qed.

Lemma decodeItemRawInputSuccessor args (prefix : byte) rest :
  decodeItemInputHead args prefix rest ->
  decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args)) ->
  0 <= decodeItemInputPointer args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) = decodeItemInputPointer args + 1.
Proof.
  intros Hhead Hlength Hp Hnowrap.
  unfold decodeItemInputHead in Hhead. rewrite Hhead in Hlength. cbn in Hlength.
  assert (Hbounds : 0 <= decodeItemInputPointer args + 1 < bv_modulus 64).
  { unfold word64Modulus in Hnowrap. change (0 <= decodeItemInputPointer args + 1 < 2^64). lia. }
  replace (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) with
    (Z_to_bv 64 (decodeItemInputPointer args + 1)) by bv_solve.
  rewrite (Z_to_bv_small 64 _ Hbounds). reflexivity.
Qed.

#[export] Hint Extern 1
  (SimplAnd (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (length (skipn (N.to_nat 8) (skipn (N.to_nat 8)
    (firstn 32 ?before ++ ?first :: ?second :: skipn ?tailOffset ?before))))))))))))))))))) = 40%nat) True) =>
  assert_fails (has_evar tailOffset);
  match goal with Hlength : length before = 40%nat |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemRawOutputExtent before first second Hlength)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer ?args)) =
    decodeItemInputPointer ?args + 0) True) =>
  unfold SimplAnd; split;
  [intros _; apply decodeItemRawInputPointer; assumption | intros _; exact I]
  : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer ?args)) 1) =
    decodeItemInputPointer ?args + 1) True) =>
  match goal with Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
    unfold SimplAnd; split;
    [intros _; apply (decodeItemRawInputSuccessor args prefix rest); assumption
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (fieldImage ?after 32 [Z_to_bv 8 0; Z_to_bv 8 0]) True) =>
  lazymatch after with
  | ?p0 :: ?p1 :: ?p2 :: ?p3 :: ?p4 :: ?p5 :: ?p6 :: ?p7 :: ?l0 :: ?l1 :: ?l2 :: ?l3 :: ?l4 :: ?l5 :: ?l6 :: ?l7 :: ?tail =>
    match goal with Hlength : length ?before = 40%nat |- _ =>
      unfold SimplAnd; split;
      [intros _; rewrite ?skipn_skipn;
       change (fieldImage ([p0; p1; p2; p3; p4; p5; p6; p7] ++ [l0; l1; l2; l3; l4; l5; l6; l7] ++ skipn 16 (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before)) 32 [Z_to_bv 8 0; Z_to_bv 8 0]);
       apply decodeItemRawOutputStatus; [exact Hlength | reflexivity | reflexivity]
      | intros _; exact I]
    end
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (preservedImage ?before ?after 17 7) True) =>
  lazymatch after with
  | ?p0 :: ?p1 :: ?p2 :: ?p3 :: ?p4 :: ?p5 :: ?p6 :: ?p7 :: ?l0 :: ?l1 :: ?l2 :: ?l3 :: ?l4 :: ?l5 :: ?l6 :: ?l7 :: ?tail =>
    match goal with Hlength : length ?before = 40%nat |- _ =>
      unfold SimplAnd; split;
      [intros _; rewrite ?skipn_skipn;
       change (preservedImage before ([p0; p1; p2; p3; p4; p5; p6; p7] ++ [l0; l1; l2; l3; l4; l5; l6; l7] ++ skipn 16 (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before)) 17 7);
       apply decodeItemRawOutputPad17; [exact Hlength | reflexivity | reflexivity]
      | intros _; exact I]
    end
  end : typeclass_instances.

#[export] Hint Extern 1 (SimplAnd (preservedImage ?before ?after 34 6) True) =>
  lazymatch after with
  | ?p0 :: ?p1 :: ?p2 :: ?p3 :: ?p4 :: ?p5 :: ?p6 :: ?p7 :: ?l0 :: ?l1 :: ?l2 :: ?l3 :: ?l4 :: ?l5 :: ?l6 :: ?l7 :: ?tail =>
    match goal with Hlength : length ?before = 40%nat |- _ =>
      unfold SimplAnd; split;
      [intros _; rewrite ?skipn_skipn;
       change (preservedImage before ([p0; p1; p2; p3; p4; p5; p6; p7] ++ [l0; l1; l2; l3; l4; l5; l6; l7] ++ skipn 16 (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before)) 34 6);
       apply decodeItemRawOutputPad34; [exact Hlength | reflexivity | reflexivity]
      | intros _; exact I]
    end
  end : typeclass_instances.

Print Assumptions decodeItemRawOutputStatus.
Print Assumptions decodeItemRawOutputPad17.
Print Assumptions decodeItemRawOutputPad34.
Print Assumptions decodeItemRawOutputExtent.
Print Assumptions decodeItemRawInputPointer.
Print Assumptions decodeItemRawInputSuccessor.
