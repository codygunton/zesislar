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

Lemma decodeItemShortClassCandidateIntro (isList : bool) args prefix rest :
  decodeItemInputHead args prefix rest ->
  (if isList then 192 else 129) <= bv_unsigned prefix <= (if isList then 247 else 183) ->
  (1 + (bv_unsigned prefix - (if isList then 192 else 128))) mod word64Modulus <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList 1 (bv_unsigned prefix - (if isList then 192 else 128)).
Proof. destruct isList; cbv beta iota zeta; decodeItemCandidateBranch. Qed.

Definition decodeItemShortStringCandidateIntro args prefix rest :=
  decodeItemShortClassCandidateIntro false args prefix rest.
Definition decodeItemShortListCandidateIntro args prefix rest :=
  decodeItemShortClassCandidateIntro true args prefix rest.



Lemma decodeItemLongClassCandidateIntro (isList : bool) args prefix rest :
  decodeItemInputHead args prefix rest ->
  (if isList then 248 else 184) <= bv_unsigned prefix <= (if isList then 255 else 191) ->
  1 + (bv_unsigned prefix - (if isList then 247 else 183)) <=
    Z.of_nat (length (decodeItemInputBytes args)) ->
  (1 + (bv_unsigned prefix - (if isList then 247 else 183)) +
    bigEndian (firstn (Z.to_nat (bv_unsigned prefix - (if isList then 247 else 183))) rest))
    mod word64Modulus <= Z.of_nat (length (decodeItemInputBytes args)) ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList (1 + (bv_unsigned prefix - (if isList then 247 else 183)))
      (bigEndian (firstn (Z.to_nat (bv_unsigned prefix - (if isList then 247 else 183))) rest)).
Proof. destruct isList; cbv beta iota zeta; decodeItemCandidateBranch. Qed.

Definition decodeItemLongStringCandidateIntro args prefix rest :=
  decodeItemLongClassCandidateIntro false args prefix rest.
Definition decodeItemLongListCandidateIntro args prefix rest :=
  decodeItemLongClassCandidateIntro true args prefix rest.




Lemma decodeItemCheckedPayloadRejected inputLength headerLength payloadLength isList :
  inputLength < (headerLength + payloadLength) mod word64Modulus ->
  checkedPayload inputLength headerLength payloadLength isList = candidateError.
Proof.
  intros Hreject. unfold checkedPayload.
  rewrite (proj2 (Z.leb_gt _ _) Hreject). reflexivity.
Qed.

Lemma decodeItemShortClassRejectedCandidateIntro (isList : bool) args prefix rest :
  decodeItemInputHead args prefix rest ->
  (if isList then 192 else 129) <= bv_unsigned prefix <= (if isList then 247 else 183) ->
  Z.of_nat (length (decodeItemInputBytes args)) <
    (1 + (bv_unsigned prefix - (if isList then 192 else 128))) mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. destruct isList; cbv beta iota zeta; decodeItemCandidateBranch. Qed.

Definition decodeItemShortStringRejectedCandidateIntro args prefix rest :=
  decodeItemShortClassRejectedCandidateIntro false args prefix rest.
Definition decodeItemShortListRejectedCandidateIntro args prefix rest :=
  decodeItemShortClassRejectedCandidateIntro true args prefix rest.





Lemma decodeItemLongClassHeaderRejectedCandidateIntro (isList : bool) args prefix rest :
  decodeItemInputHead args prefix rest ->
  (if isList then 248 else 184) <= bv_unsigned prefix <= (if isList then 255 else 191) ->
  Z.of_nat (length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - (if isList then 247 else 183)) ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. destruct isList; cbv beta iota zeta; decodeItemCandidateBranch. Qed.

Definition decodeItemLongStringHeaderRejectedCandidateIntro args prefix rest :=
  decodeItemLongClassHeaderRejectedCandidateIntro false args prefix rest.
Definition decodeItemLongListHeaderRejectedCandidateIntro args prefix rest :=
  decodeItemLongClassHeaderRejectedCandidateIntro true args prefix rest.





Lemma decodeItemLongClassPayloadRejectedCandidateIntro (isList : bool) args prefix rest :
  decodeItemInputHead args prefix rest ->
  (if isList then 248 else 184) <= bv_unsigned prefix <= (if isList then 255 else 191) ->
  1 + (bv_unsigned prefix - (if isList then 247 else 183)) <= Z.of_nat (length (decodeItemInputBytes args)) ->
  Z.of_nat (length (decodeItemInputBytes args)) <
    (1 + (bv_unsigned prefix - (if isList then 247 else 183)) +
      bigEndian (firstn (Z.to_nat (bv_unsigned prefix - (if isList then 247 else 183))) rest))
      mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError.
Proof. destruct isList; cbv beta iota zeta; decodeItemCandidateBranch. Qed.

Definition decodeItemLongStringPayloadRejectedCandidateIntro args prefix rest :=
  decodeItemLongClassPayloadRejectedCandidateIntro false args prefix rest.
Definition decodeItemLongListPayloadRejectedCandidateIntro args prefix rest :=
  decodeItemLongClassPayloadRejectedCandidateIntro true args prefix rest.






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
