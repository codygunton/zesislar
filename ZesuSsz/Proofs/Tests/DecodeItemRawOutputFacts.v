Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.ResultImage.
From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Lemma rawOutputRegistrationOff (before : list byte) : length before = 40%nat -> True.
Proof.
  intros Hlength.
  let target := constr:(SimplAnd
    (16 + length (skipn (N.to_nat 8) (skipn (N.to_nat 8)
      (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before))) = 40)%nat True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Require Import ZesuSsz.Compliance.DecodeItemRawOutputFacts.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.

Ltac raw_output_registered :=
  cbn [app length];
  match goal with |- ?P =>
    let target := constr:(SimplAnd P True) in
    let evidence := constr:(_ : target) in exact (proj1 evidence I)
  end.

Section Storage.
Context (before : list byte) (p0 p1 p2 p3 p4 p5 p6 p7 l0 l1 l2 l3 l4 l5 l6 l7 : byte).

Lemma rawOutputStatusOn (Hlength : length before = 40%nat) :
  fieldImage ([p0; p1; p2; p3; p4; p5; p6; p7; l0; l1; l2; l3; l4; l5; l6; l7] ++
    skipn (N.to_nat 8) (skipn (N.to_nat 8)
      (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before))) 32 [Z_to_bv 8 0; Z_to_bv 8 0].
Proof using All. raw_output_registered. Qed.

Lemma rawOutputPad17On (Hlength : length before = 40%nat) :
  preservedImage before ([p0; p1; p2; p3; p4; p5; p6; p7; l0; l1; l2; l3; l4; l5; l6; l7] ++
    skipn (N.to_nat 8) (skipn (N.to_nat 8)
      (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before))) 17 7.
Proof using All. raw_output_registered. Qed.

Lemma rawOutputPad34On (Hlength : length before = 40%nat) :
  preservedImage before ([p0; p1; p2; p3; p4; p5; p6; p7; l0; l1; l2; l3; l4; l5; l6; l7] ++
    skipn (N.to_nat 8) (skipn (N.to_nat 8)
      (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before))) 34 6.
Proof using All. raw_output_registered. Qed.

Lemma rawOutputExtentOn (Hlength : length before = 40%nat) :
  length ([p0; p1; p2; p3; p4; p5; p6; p7; l0; l1; l2; l3; l4; l5; l6; l7] ++
    skipn (N.to_nat 8) (skipn (N.to_nat 8)
      (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before))) = 40%nat.
Proof using All. raw_output_registered. Qed.
End Storage.

Lemma rawInputPointerOn args :
  0 <= decodeItemInputPointer args -> 0 <= decodeItemInputLength args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = decodeItemInputPointer args + 0.
Proof. intros. raw_output_registered. Qed.

Lemma rawInputSuccessorOn args prefix rest :
  decodeItemInputHead args prefix rest ->
  decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args)) ->
  0 <= decodeItemInputPointer args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) = decodeItemInputPointer args + 1.
Proof. intros. raw_output_registered. Qed.

Lemma rawOutputMissingLength (before : list byte) : True.
Proof.
  let target := constr:(SimplAnd
    (16 + length (skipn (N.to_nat 8) (skipn (N.to_nat 8)
      (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 34 before))) = 40)%nat True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma rawInputMissingBounds (args : DecodeItemArgs) : True.
Proof.
  let target := constr:(SimplAnd
    (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = decodeItemInputPointer args + 0) True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma rawOutputWrongTail (before : list byte) : length before = 40%nat -> True.
Proof.
  intros Hlength.
  let target := constr:(SimplAnd
    (16 + length (skipn (N.to_nat 8) (skipn (N.to_nat 8)
      (firstn 32 before ++ [Z_to_bv 8 0; Z_to_bv 8 0] ++ skipn 35 before))) = 40)%nat True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Print Assumptions rawOutputRegistrationOff.
Print Assumptions rawOutputStatusOn.
Print Assumptions rawOutputPad17On.
Print Assumptions rawOutputPad34On.
Print Assumptions rawOutputExtentOn.
Print Assumptions rawInputPointerOn.
Print Assumptions rawInputSuccessorOn.
Print Assumptions rawOutputMissingLength.
Print Assumptions rawInputMissingBounds.
Print Assumptions rawOutputWrongTail.
