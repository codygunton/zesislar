Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Import ListNotations.
Open Scope Z_scope.

(* These lemmas derive candidate facts from input and branch guards.
   Sail evaluation remains a separate semantic obligation. *)
Local Ltac decodeItemCandidateBranch :=
  intros Hinput Hclass; intros;
  unfold decodeItemInputHead in Hinput;
  rewrite Hinput in *;
  unfold candidateDecodeItem, checkedPayload; cbv beta iota zeta;
  repeat lazymatch goal with
  | |- (if ?condition then _ else _) = _ =>
    let Hcondition := fresh "Hcondition" in
    first [assert (Hcondition : condition = true) by
             (first [apply Z.leb_le | apply Z.eqb_eq]; first [assumption | lia])
          |assert (Hcondition : condition = false) by
             (first [apply Z.leb_gt | apply Z.eqb_neq]; first [assumption | lia])];
    rewrite Hcondition; cbv beta iota zeta
  end; reflexivity.

Lemma decodeItemLiteralCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 0 1.
Proof. decodeItemCandidateBranch. Qed.

Lemma decodeItemEmptyCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest -> bv_unsigned prefix = 128 ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 1 0.
Proof. decodeItemCandidateBranch. Qed.

Lemma decodeItemShortStringCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  (1 + (bv_unsigned prefix - 128)) mod word64Modulus <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess false 1 (bv_unsigned prefix - 128).
Proof. decodeItemCandidateBranch. Qed.

Lemma decodeItemShortListCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  (1 + (bv_unsigned prefix - 192)) mod word64Modulus <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess true 1 (bv_unsigned prefix - 192).
Proof. decodeItemCandidateBranch. Qed.

Lemma decodeItemLongStringCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  1 + (bv_unsigned prefix - 183) <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  (1 + (bv_unsigned prefix - 183) +
    bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest))
    mod word64Modulus <= Z.of_nat (length (decodeItemInputBytes args)) ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess false (1 + (bv_unsigned prefix - 183))
      (bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)).
Proof. decodeItemCandidateBranch. Qed.

Lemma decodeItemLongListCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  1 + (bv_unsigned prefix - 247) <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  (1 + (bv_unsigned prefix - 247) +
    bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest))
    mod word64Modulus <= Z.of_nat (length (decodeItemInputBytes args)) ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess true (1 + (bv_unsigned prefix - 247))
      (bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)).
Proof. decodeItemCandidateBranch. Qed.


Lemma decodeItemCheckedPayloadRejected inputLength headerLength payloadLength isList :
  inputLength < (headerLength + payloadLength) mod word64Modulus ->
  checkedPayload inputLength headerLength payloadLength isList = candidateError.
Proof.
  intros Hreject. unfold checkedPayload.
  rewrite (proj2 (Z.leb_gt _ _) Hreject). reflexivity.
Qed.

Lemma decodeItemShortStringRejectedCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  Z.of_nat (length (decodeItemInputBytes args)) <
    (1 + (bv_unsigned prefix - 128)) mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. decodeItemCandidateBranch. Qed.


Lemma decodeItemShortListRejectedCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  Z.of_nat (length (decodeItemInputBytes args)) <
    (1 + (bv_unsigned prefix - 192)) mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. decodeItemCandidateBranch. Qed.


Lemma decodeItemLongStringHeaderRejectedCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  Z.of_nat (length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 183) ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. decodeItemCandidateBranch. Qed.


Lemma decodeItemLongListHeaderRejectedCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  Z.of_nat (length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 247) ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. decodeItemCandidateBranch. Qed.


Lemma decodeItemLongStringPayloadRejectedCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  184 <= bv_unsigned prefix <= 191 ->
  1 + (bv_unsigned prefix - 183) <= Z.of_nat (length (decodeItemInputBytes args)) ->
  Z.of_nat (length (decodeItemInputBytes args)) <
    (1 + (bv_unsigned prefix - 183) +
      bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest))
      mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. decodeItemCandidateBranch. Qed.


Lemma decodeItemLongListPayloadRejectedCandidateIntro args prefix rest :
  decodeItemInputHead args prefix rest ->
  248 <= bv_unsigned prefix <= 255 ->
  1 + (bv_unsigned prefix - 247) <= Z.of_nat (length (decodeItemInputBytes args)) ->
  Z.of_nat (length (decodeItemInputBytes args)) <
    (1 + (bv_unsigned prefix - 247) +
      bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest))
      mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. decodeItemCandidateBranch. Qed.



Lemma decodeItemDomainInputLengthBounds args :
  decodeItemC1BDomain args ->
  0 <= decodeItemInputLength args <= 0x40000000.
Proof.
  intros Hdomain.
  unfold decodeItemC1BDomain, decodeItemArgsWellFormed in Hdomain.
  destruct Hdomain as [Hlength [Hstorage Hlayout]].
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as
    (Hpointer & Hnonnegative & Hnowrap & Houtput & HoutputEnd &
     Hstack & HstackBase & HstackEnd & Hseparation1 & Hseparation2 &
     Hseparation3 & Hreturn & Halignment & Hreadable & HoutputBase &
     HoutputBound & HinputEnd & HsliceEnd).
  change ((0x40000000 <= decodeItemInputPointer args /\
           decodeItemInputPointer args + decodeItemInputLength args <= 0x80000000) \/
          (0xa0000000 <= decodeItemInputPointer args /\
           decodeItemInputPointer args + decodeItemInputLength args <= 0xc0000000))
    in Hreadable.
  destruct Hreadable as [[Hbase Hend]|[Hbase Hend]]; lia.
Qed.

Lemma decodeItemEmptyInputRejected args :
  decodeItemInputBytes args = [] -> decodeItemRejectedFacts args.
Proof.
  intros Hinput.
  unfold decodeItemRejectedFacts, decodeItemSailCursor.
  rewrite Hinput. split; [reflexivity|vm_compute; reflexivity].
Qed.

Lemma decodeItemDomainNonemptyInputHead returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
  exists prefix rest, decodeItemInputHead args prefix rest.
Proof.
  intros Hdomain Hnonzero.
  unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed in Hdomain.
  destruct Hdomain as [_ [Hlength Hfacts]].
  destruct (decodeItemInputBytes args) as [|prefix rest] eqn:Hinput.
  - simpl in Hlength.
    rewrite Hlength in Hnonzero. exfalso. apply Hnonzero. reflexivity.
  - exists prefix, rest. exact Hinput.
Qed.
