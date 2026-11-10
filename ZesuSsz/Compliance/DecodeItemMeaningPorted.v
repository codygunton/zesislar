(* Ported pure meaning lemmas: verbatim copies of October modules (see PORT.json).
   It imports neither core umbrella. *)
Require ZesuSsz.Automation.Hooks.
From Coq Require List Lia ZArith.
From stdpp Require bitvector.definitions.
Require SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require ZesuSsz.Contracts.ResultImage.
Require ZesuSsz.Contracts.RlpDecodeItem.
Require ZesuSsz.Contracts.RlpDecodeItemSchema.
Require ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
From Coq Require List ZArith Lia.
Require ZesuSsz.Contracts.DecodeItemReturnFacts.
Require ZesuSsz.Contracts.RlpDecodeItemContract.
Require ZesuSsz.Automation.SailEval.
From Coq Require Bool List String ZArith Lia.
Require SailStdpp.MachineWord SailStdpp.Prompt_monad.
Require SailStdpp.Prompt.
Require SailStdpp.Operators_mwords.
Require EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require ZesuSsz.Compliance.SailRun.
Require ZesuSsz.Compliance.RlpInputBounds.
Require ZesuMachineMap.Machine.
From Coq Require Lia List ZArith.
Require SailStdpp.MachineWord.
Require EvmSailRlp.evm_rlp_types.
Require ZesuSsz.Compliance.KnownBugs.
From Coq Require ZArith.
Require isla.riscv64.riscv64.

(* Verbatim copy of ZesuSsz/Contracts/RlpDecodeItemReturnImages.v. *)
Module PortedReturnImages.
Import ZesuSsz.Automation.Hooks.
From Coq Require Import List Lia ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Import ListNotations.
Open Scope Z_scope.

Lemma fieldImage_middle prefix field suffix :
  fieldImage (prefix ++ field ++ suffix) (length prefix) field.
Proof.
  intros i Hi.
  rewrite nth_error_app2 by lia.
  replace (length prefix + i - length prefix)%nat with i by lia.
  rewrite nth_error_app1 by lia.
  reflexivity.
Qed.

Lemma selectedPadLength (before : list byte) offset count :
  (length before = 40)%nat ->
  (offset + count <= 40)%nat ->
  (length (firstn count (skipn offset before)) = count)%nat.
Proof.
  intros Hbefore Hrange.
  rewrite firstn_length, skipn_length, Hbefore.
  lia.
Qed.

Lemma decodeItemOkBytes_length before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  (length (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList) = 40)%nat.
Proof.
  intros Hbefore Hp Hl Hc.
  unfold decodeItemOkBytes.
  repeat rewrite app_length.
  rewrite (selectedPadLength before 17 7),
          (selectedPadLength before 34 6) by lia.
  simpl. lia.
Qed.

Ltac decodeItemReturnField :=
  repeat match goal with |- length _ = _ -> _ => intro end;
  unfold decodeItemOkBytes;
  lazymatch goal with |- fieldImage ?image ?offset ?field =>
    let finish prefix suffix := (
      replace image with (prefix ++ field ++ suffix) by
        (repeat rewrite app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity);
      replace offset with (length prefix) by
        (
        repeat rewrite app_length;
        rewrite ?firstn_length; rewrite ?skipn_length;
        repeat match goal with H : length ?l = ?n |- context [length ?l] => rewrite H end;
        cbn; lia);
      apply fieldImage_middle) in
    let rec seek prefix remaining :=
      lazymatch remaining with
      | ?head ++ ?tail =>
          first [constr_eq head field; finish prefix tail |
            let prefix := constr:(prefix ++ head) in seek prefix tail]
      | _ => constr_eq remaining field; finish prefix constr:([] : list byte)
      end in
    seek constr:([] : list byte) image
  end.

Lemma decodeItemOkBytes_pointer before pointerBytes lengthBytes consumedBytes isList :
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    0 pointerBytes.
Proof. decodeItemReturnField. Qed.

Lemma decodeItemOkBytes_length_field before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    8 lengthBytes.
Proof. decodeItemReturnField. Qed.

Lemma decodeItemOkBytes_consumed_field before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    24 consumedBytes.
Proof. decodeItemReturnField. Qed.

Lemma preservedImage_of_slice before after offset count :
  (length before = 40)%nat ->
  (offset + count <= 40)%nat ->
  fieldImage after offset (firstn count (skipn offset before)) ->
  preservedImage before after offset count.
Proof.
  intros Hbefore Hrange Hfield i Hi.
  assert (Hpad : (i < length (firstn count (skipn offset before)))%nat).
  { rewrite (selectedPadLength before offset count); lia. }
  specialize (Hfield i Hpad).
  rewrite nth_error_firstn_inside in Hfield by exact Hi.
  rewrite nth_error_skipn_offset in Hfield.
  exact Hfield.
Qed.

Lemma decodeItemOkBytes_flag_field before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    16 [Z_to_bv 8 (if isList then 1 else 0)].
Proof. decodeItemReturnField. Qed.

Lemma decodeItemOkBytes_pad17_field before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    17 (firstn 7 (skipn 17 before)).
Proof. decodeItemReturnField. Qed.

Lemma decodeItemOkBytes_status_field before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    32 [Z_to_bv 8 0; Z_to_bv 8 0].
Proof. decodeItemReturnField. Qed.

Lemma decodeItemOkBytes_pad34_field before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  fieldImage (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    34 (firstn 6 (skipn 34 before)).
Proof. decodeItemReturnField. Qed.

Lemma byteAt_from_singleton_image after offset value :
  fieldImage after offset [Z_to_bv 8 value] ->
  bv_unsigned (Z_to_bv 8 value) = value ->
  byteAt after offset value.
Proof.
  intros Hfield Hvalue.
  specialize (Hfield 0%nat ltac:(simpl; lia)).
  replace (offset + 0)%nat with offset in Hfield by lia.
  unfold byteAt. rewrite Hfield. simpl. now rewrite Hvalue.
Qed.

Lemma decodeItemOkBytes_flag before pointerBytes lengthBytes consumedBytes isList :
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  byteAt (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    16 (if isList then 1 else 0).
Proof.
  intros Hp Hl.
  apply byteAt_from_singleton_image.
  - apply decodeItemOkBytes_flag_field; assumption.
  - destruct isList; reflexivity.
Qed.

Lemma decodeItemOkBytes_status before pointerBytes lengthBytes consumedBytes isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  byteAt (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    32 0 /\
  byteAt (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    33 0.
Proof.
  intros Hbefore Hp Hl Hc.
  pose proof (decodeItemOkBytes_status_field before pointerBytes lengthBytes
    consumedBytes isList Hbefore Hp Hl Hc) as Hfield.
  split; unfold byteAt.
  - specialize (Hfield 0%nat ltac:(simpl; lia)).
    replace (32 + 0)%nat with 32%nat in Hfield by lia.
    rewrite Hfield. reflexivity.
  - specialize (Hfield 1%nat ltac:(simpl; lia)).
    replace (32 + 1)%nat with 33%nat in Hfield by lia.
    rewrite Hfield. reflexivity.
Qed.

Lemma decodeItemOkBytes_success before pointerBytes lengthBytes consumedBytes
    payloadPointer payloadLength consumed isList :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = payloadPointer ->
  littleEndian lengthBytes = payloadLength ->
  littleEndian consumedBytes = consumed ->
  successResult40 before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    payloadPointer payloadLength isList consumed.
Proof.
  intros Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply (successResult40_from_images before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    pointerBytes lengthBytes consumedBytes); try assumption.
  - apply decodeItemOkBytes_length; assumption.
  - apply decodeItemOkBytes_pointer.
  - apply decodeItemOkBytes_length_field; assumption.
  - apply decodeItemOkBytes_consumed_field; assumption.
  - apply decodeItemOkBytes_flag; assumption.
  - apply (decodeItemOkBytes_status before pointerBytes lengthBytes
      consumedBytes isList); assumption.
  - apply (decodeItemOkBytes_status before pointerBytes lengthBytes
      consumedBytes isList); assumption.
  - apply (preservedImage_of_slice before _ 17 7); try lia.
    apply decodeItemOkBytes_pad17_field; assumption.
  - apply (preservedImage_of_slice before _ 34 6); try lia.
    apply decodeItemOkBytes_pad34_field; assumption.
Qed.

Lemma decodeItemOkBytes_encodeSuccess inputPointer input before
    pointerBytes lengthBytes consumedBytes isList headerLength payloadLength :
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes =
    itemPayloadPointer inputPointer input headerLength ->
  littleEndian lengthBytes = payloadLength ->
  littleEndian consumedBytes =
    (headerLength + payloadLength) mod word64Modulus ->
  encodeResult inputPointer input before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes isList)
    (candidateSuccess isList headerLength payloadLength).
Proof.
  intros Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply encodeResult_success_from_padding.
  - apply (decodeItemOkBytes_success before pointerBytes lengthBytes
      consumedBytes); assumption.
  - apply (preservedImage_of_slice before _ 17 7); try lia.
    apply decodeItemOkBytes_pad17_field; assumption.
  - apply (preservedImage_of_slice before _ 34 6); try lia.
    apply decodeItemOkBytes_pad34_field; assumption.
Qed.

Lemma errorEncoding_valueImage :
  valueImage errorEncoding 0 40
    (fun i => if Nat.eqb i 32 then 4 else 0).
Proof.
  intros i Hi.
  unfold byteAt, errorEncoding.
  replace (0 + i)%nat with i by lia.
  destruct (Nat.lt_trichotomy i 32) as [Hsmall|[Heq|Hlarge]].
  - rewrite nth_error_app1 by (rewrite repeat_length; lia).
    rewrite nth_error_repeat by lia.
    replace (Nat.eqb i 32) with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  - subst i.
    rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length. simpl.
    reflexivity.
  - rewrite nth_error_app2 by (rewrite repeat_length; lia).
    rewrite repeat_length.
    rewrite nth_error_app2 by (simpl; lia).
    change (length [Values.mword_of_int 4]) with 1%nat.
    rewrite nth_error_repeat by lia.
    replace (Nat.eqb i 32) with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
Qed.

Lemma errorReturnImage :
  errorResult40 errorEncoding /\
  forall inputPointer input before,
    encodeResult inputPointer input before errorEncoding candidateError.
Proof.
  split.
  - apply errorResult40_from_pointwise.
    + apply errorEncoding_length.
    + apply errorEncoding_valueImage.
  - intros.
    apply encodeResult_error_from_pointwise.
    + apply errorEncoding_length.
    + change (fieldImage (([] : list byte) ++ errorEncoding ++ [])
        (length ([] : list byte)) errorEncoding).
      apply fieldImage_middle.
Qed.


(* Return 0x800d69a0 has literal and short-string incoming edges. *)


(* Return 0x800d69d4 uses the selected empty-string pointer sentinel. *)
Lemma return_800d69d4_emptyString inputPointer prefix rest before
    pointerBytes lengthBytes consumedBytes :
  bv_unsigned prefix = 128 ->
  (length before = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = 1 ->
  littleEndian lengthBytes = 0 ->
  littleEndian consumedBytes = 1 mod word64Modulus ->
  encodeResult inputPointer (prefix :: rest) before
    (decodeItemOkBytes before pointerBytes lengthBytes consumedBytes false)
    (candidateSuccess false 1 0).
Proof.
  intros Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv.
  apply decodeItemOkBytes_encodeSuccess; try assumption.
  unfold itemPayloadPointer. simpl. rewrite Hprefix, Hpv. reflexivity.
Qed.

(* The long-string and long-list sites retain modular consumed length. *)
End PortedReturnImages.

(* Verbatim copy of ZesuSsz/Compliance/DecodeItemSemanticIntroduction.v. *)
Module PortedSemanticIntroduction.
Import ZesuSsz.Automation.Hooks.
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
End PortedSemanticIntroduction.

(* Verbatim copy of ZesuSsz/Compliance/DecodeItemSailEvaluation.v. *)
Module PortedSailEvaluation.
Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.SailEval.
From Coq Require Import Bool List String ZArith Lia.
Require Import SailStdpp.MachineWord SailStdpp.Prompt_monad.
Require Import SailStdpp.Prompt.
Require Import SailStdpp.Operators_mwords.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuMachineMap.Machine.
Import PortedSemanticIntroduction.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

#[local] Hint Unfold EvmSailRlp.evm_rlp.rlp_ref_hdr
  EvmSailRlp.evm_rlp.rlp_decode_item
  EvmSailRlp.evm_rlp.stateless_input_slice_byte
  EvmSailRlp.evm_rlp.stateless_input_byte_at
  EvmSailRlp.evm_rlp_types.returnM EvmSailRlp.evm_rlp_types.read_reg : sail.
#[local] Hint Rewrite shimInputLengthExact : zesu_sail.

Lemma decodeItemRunPromptBindSuccess {A B} (action : M A) (next : A -> M B)
    rs value rs' :
  runPrompt action rs true = (Success value, rs') ->
  runPrompt (SailStdpp.Prompt_monad.bind action next) rs true =
    runPrompt (next value) rs' true.
Proof.
  intros Hrun. etransitivity; [apply sail_run_bind |].
  rewrite Hrun. reflexivity.
Qed.

Print Assumptions decodeItemRunPromptBindSuccess.

Lemma decodeItemRunPromptHeadByte prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  runPrompt (EvmSailRlp.evm_rlp.stateless_input_slice_byte slice 0) rs true =
    (Success prefix, rs).
Proof. sail_eval. Qed.

Print Assumptions decodeItemRunPromptHeadByte.

Lemma decodeItemUintByte (value : byte) : uint value = bv_unsigned value.
Proof. apply sail_uint_unsigned. Qed.

Lemma decodeItemRunPromptLiteralHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  bv_unsigned prefix <= 127 ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (false, Build_source_pointer 0, 1), rs).
Proof. sail_eval. Qed.

Print Assumptions decodeItemUintByte.
Print Assumptions decodeItemRunPromptLiteralHeader.

Lemma decodeItemRunPromptShortStringHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  128 <= bv_unsigned prefix <= 183 ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (false, Build_source_pointer 1, bv_unsigned prefix - 128), rs).
Proof. sail_eval. Qed.

Lemma decodeItemRunPromptShortListHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  192 <= bv_unsigned prefix <= 247 ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (true, Build_source_pointer 1, bv_unsigned prefix - 192), rs).
Proof. sail_eval. Qed.

Definition decodeItemInstalledState bytes : regstate :=
  register_set shim_input_bytes bytes
    (register_set k_execution_profile EvmSailRlp.evm_rlp.DEFAULT_EXECUTION_PROFILE
      (register_set shim_input_bytes [] init_regstate)).

Lemma decodeItemRunPromptInitialized bytes :
  runPrompt (initializedInput bytes) init_regstate true =
    (Success tt, decodeItemInstalledState bytes).
Proof.
  reflexivity.
Qed.

Lemma decodeItemInstalledBytes bytes :
  register_lookup shim_input_bytes (decodeItemInstalledState bytes) = bytes.
Proof.
  unfold decodeItemInstalledState. apply register_lookup_set.
Qed.

Print Assumptions decodeItemRunPromptShortStringHeader.
Print Assumptions decodeItemRunPromptShortListHeader.
Print Assumptions decodeItemRunPromptInitialized.
Print Assumptions decodeItemInstalledBytes.

Lemma decodeItemRunPromptAcceptedHeader (prefix : byte) (rest : list byte)
    rs isList headerLength payloadLength
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (isList, Build_source_pointer headerLength, payloadLength), rs) ->
  0 <= headerLength -> 0 <= payloadLength ->
  0 < headerLength + payloadLength ->
  headerLength + payloadLength <= Z.of_nat (List.length (prefix :: rest)) ->
  exists fullLength contentLength (field : RlpFieldRef 0 fullLength contentLength),
    runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item slice) rs true =
      (Success (@existT Z (fun full => {content : Z & RlpFieldRef 0 full content})
        fullLength (@existT Z (fun content => RlpFieldRef 0 fullLength content)
          contentLength field)), rs) /\
    RlpFieldRef_is_list field = isList /\
    fullLength - contentLength = headerLength /\ contentLength = payloadLength.
Proof.
  intros Hlength Hheader Hnonnegative Hpayload Hpositive Hfits.
  exists (headerLength + payloadLength), payloadLength. eexists. split.
  - unfold EvmSailRlp.evm_rlp.rlp_decode_item.
    cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM
      SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind].
    erewrite decodeItemRunPromptBindSuccess with
      (value := (isList, headerLength, payloadLength)) (rs' := rs).
    + rewrite (proj2 (Z.ltb_ge (Z.of_nat (List.length (prefix :: rest))) headerLength) ltac:(lia)).
      rewrite (proj2 (Z.ltb_ge (Z.of_nat (List.length (prefix :: rest)) - headerLength) payloadLength) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt 0 (headerLength + payloadLength)) Hpositive).
      rewrite (proj2 (Z.leb_le _ _) Hfits). reflexivity.
    + erewrite decodeItemRunPromptBindSuccess with
        (value := (isList, Build_source_pointer headerLength, payloadLength))
        (rs' := rs); last exact Hheader.
      reflexivity.
  - simpl. repeat split; lia.
Qed.

Print Assumptions decodeItemRunPromptAcceptedHeader.

Lemma decodeItemSailInputLengthBound args :
  decodeItemC1BDomain args ->
  Z.of_nat (List.length (decodeItemInputBytes args)) <= stateless_input_region_bound.
Proof.
  intros Hdomain.
  pose proof (decodeItemDomainInputLengthBounds args Hdomain) as Hbound.
  destruct Hdomain as [Hlength _].
  rewrite <- Hlength. unfold stateless_input_region_bound. lia.
Qed.

Lemma decodeItemSailInputSliceValid args :
  decodeItemC1BDomain args ->
  validInputSlice (decodeItemInputBytes args) 0
    (Z.of_nat (List.length (decodeItemInputBytes args))) = true.
Proof.
  intros Hdomain. pose proof (decodeItemSailInputLengthBound args Hdomain) as Hbound.
  unfold validInputSlice. simpl.
  rewrite (proj2 (Z.leb_le 0 _) (Nat2Z.is_nonneg _)).
  rewrite (proj2 (Z.leb_le _ _) Hbound). rewrite Z.leb_refl. reflexivity.
Qed.

Print Assumptions decodeItemSailInputLengthBound.
Print Assumptions decodeItemSailInputSliceValid.

Lemma decodeItemRunPromptShimByte bytes index value rs :
  nth_error bytes index = Some value ->
  runPrompt (EvmSailRlp.evm_rlp.shim_byte_at bytes (Z.of_nat index)) rs true =
    (Success value, rs).
Proof. apply sail_run_shim_byte_nat. Qed.

Lemma decodeItemRunPromptSliceByte bytes base len off value rs
    (slice : StatelessInputSliceFields base len) :
  register_lookup shim_input_bytes rs = bytes ->
  0 <= base -> 0 <= len -> base + len <= Z.of_nat (List.length bytes) ->
  0 <= off < len -> nth_error bytes (Z.to_nat (base + off)) = Some value ->
  runPrompt (EvmSailRlp.evm_rlp.stateless_input_slice_byte slice off) rs true =
    (Success value, rs).
Proof. sail_eval. eapply sail_run_shim_byte; [lia | eassumption]. Qed.

Print Assumptions decodeItemRunPromptShimByte.
Print Assumptions decodeItemRunPromptSliceByte.

Lemma decodeItemRunPromptRejectedHeader (prefix : byte) (rest : list byte)
    rs isList headerLength payloadLength
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (isList, Build_source_pointer headerLength, payloadLength), rs) ->
  Z.of_nat (List.length (prefix :: rest)) < headerLength + payloadLength ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item slice) rs true = (Reject RlpDecode, rs).
Proof.
  intros Hheader Hreject.
  unfold EvmSailRlp.evm_rlp.rlp_decode_item.
  cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM
    SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind].
  erewrite decodeItemRunPromptBindSuccess with
    (value := (isList, headerLength, payloadLength)) (rs' := rs).
  - destruct (Z.of_nat (List.length (prefix :: rest)) <? headerLength) eqn:Hguard.
    + reflexivity.
    + apply Z.ltb_ge in Hguard.
      rewrite (proj2 (Z.ltb_lt
        (Z.of_nat (List.length (prefix :: rest)) - headerLength) payloadLength) ltac:(lia)).
      reflexivity.
  - erewrite decodeItemRunPromptBindSuccess with
      (value := (isList, Build_source_pointer headerLength, payloadLength))
      (rs' := rs); last exact Hheader.
    reflexivity.
Qed.

Print Assumptions decodeItemRunPromptRejectedHeader.

Lemma decodeItemRunPromptBindReject {A B} (action : M A) (next : A -> M B)
    rs reason rs' :
  runPrompt action rs true = (Reject reason, rs') ->
  runPrompt (SailStdpp.Prompt_monad.bind action next) rs true = (Reject reason, rs').
Proof. intros Hrun. rewrite sail_run_bind. rewrite Hrun. reflexivity. Qed.

Print Assumptions decodeItemRunPromptBindReject.

Lemma decodeItemRunPromptHeaderReject (prefix : byte) (rest : list byte)
    rs (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true = (Reject RlpDecode, rs) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item slice) rs true = (Reject RlpDecode, rs).
Proof.
  intros Hheader.
  unfold EvmSailRlp.evm_rlp.rlp_decode_item.
  cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM
    SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind].
  rewrite (proj2 (Z.eqb_neq (Z.of_nat (List.length (prefix :: rest))) 0)
    ltac:(cbn [List.length]; rewrite Nat2Z.inj_succ; lia)).
  cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM SailStdpp.Prompt_monad.returnm
    SailStdpp.Prompt_monad.bind].
  apply decodeItemRunPromptBindReject.
  apply decodeItemRunPromptBindReject. exact Hheader.
Qed.

Print Assumptions decodeItemRunPromptHeaderReject.
End PortedSailEvaluation.

(* Verbatim copy of ZesuSsz/Compliance/DecodeItemSailIntroduction.v up to decodeItemLongCandidateFromProvenance. *)
Module PortedSailIntroduction.
Import ZesuSsz.Automation.Hooks.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.SailRun.
Import PortedSailEvaluation.
Import PortedSemanticIntroduction.
Require Import ZesuSsz.Automation.SailEval.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Import ListNotations.
Open Scope Z_scope.

Lemma decodeItemSailSuccessFromPrompt args isList headerLength payloadLength :
  decodeItemC1BDomain args ->
  (exists fullLength contentLength (field : RlpFieldRef 0 fullLength contentLength),
    runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item (decodeItemSailCursor args))
      (decodeItemInstalledState (decodeItemInputBytes args)) true =
      (Success (@existT Z (fun full => {content : Z & RlpFieldRef 0 full content})
        fullLength (@existT Z (fun content => RlpFieldRef 0 fullLength content)
          contentLength field)), decodeItemInstalledState (decodeItemInputBytes args)) /\
    RlpFieldRef_is_list field = isList /\
    fullLength - contentLength = headerLength /\ contentLength = payloadLength) ->
  decodeItemSailSuccess args isList headerLength payloadLength.
Proof.
  intros Hdomain [fullLength [contentLength [field [Hrun Hfacts]]]].
  exists fullLength, contentLength, field. split; last exact Hfacts.
  unfold runRlpDecodeItem, SailRun.runDecoder.
  rewrite (decodeItemSailInputSliceValid args Hdomain).
  unfold SailStdpp.Prompt_monad.bind0.
  erewrite decodeItemRunPromptBindSuccess with (value := tt)
    (rs' := decodeItemInstalledState (decodeItemInputBytes args));
    last apply decodeItemRunPromptInitialized.
  rewrite Hrun. reflexivity.
Qed.

Lemma decodeItemSailRejectFromPrompt args :
  decodeItemC1BDomain args ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item (decodeItemSailCursor args))
    (decodeItemInstalledState (decodeItemInputBytes args)) true =
    (Reject RlpDecode, decodeItemInstalledState (decodeItemInputBytes args)) ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) = Reject RlpDecode.
Proof.
  intros Hdomain Hrun. unfold runRlpDecodeItem, SailRun.runDecoder.
  rewrite (decodeItemSailInputSliceValid args Hdomain).
  unfold SailStdpp.Prompt_monad.bind0.
  erewrite decodeItemRunPromptBindSuccess with (value := tt)
    (rs' := decodeItemInstalledState (decodeItemInputBytes args));
    last apply decodeItemRunPromptInitialized.
  rewrite Hrun. reflexivity.
Qed.

Import ListNotations.
Open Scope Z_scope.
#[local] Hint Unfold EvmSailRlp.evm_rlp.rlp_ref_hdr
  EvmSailRlp.evm_rlp.stateless_input_slice_byte
  EvmSailRlp.evm_rlp.stateless_input_byte_at
  EvmSailRlp.evm_rlp_types.returnM EvmSailRlp.evm_rlp_types.read_reg
  EvmSailRlp.evm_rlp.rlp_uint64_width
  EvmSailRlp.evm_rlp.stateless_input_sub_slice
  EvmSailRlp.evm_rlp.rlp_uint64_append bigEndian : sail.
#[local] Hint Rewrite shimInputLengthExact : zesu_sail.
#[local] Hint Unfold EvmSailRlp.evm_rlp._rec_rlp_uint64_width : zesu_sail_rec.

#[local] Hint Rewrite decodeItemInstalledBytes : zesu_sail.

Ltac decodeItemSailBranch candidate execution :=
  intros Hdomain Hinput Hclass; intros;
  lazymatch goal with
  | |- decodeItemAcceptedFacts _ _ _ _ =>
      split;
      [eapply candidate; eauto;
        try (rewrite Z.mod_small; [assumption | lia]) |
       eapply execution; eauto]
  | |- decodeItemSailSuccess _ _ _ _ =>
      apply decodeItemSailSuccessFromPrompt; [exact Hdomain |];
      unfold decodeItemInputHead in Hinput; unfold decodeItemSailCursor;
      rewrite Hinput in *;
      eapply decodeItemRunPromptAcceptedHeader;
      first [solve [assumption] | solve [reflexivity] | solve [lia] | solve [simpl; lia] |
        solve [apply execution; try reflexivity; auto using decodeItemInstalledBytes; lia]]
  | |- decodeItemRejectedFacts _ =>
      split;
      [eapply candidate; eauto;
        try (rewrite Z.mod_small; [assumption | lia]) |
       apply decodeItemSailRejectFromPrompt; [exact Hdomain |];
       unfold decodeItemInputHead in Hinput; unfold decodeItemSailCursor;
       rewrite Hinput in *;
       first [eapply decodeItemRunPromptRejectedHeader;
         [solve [apply execution; try reflexivity; auto using decodeItemInstalledBytes; lia] | assumption] |
         apply decodeItemRunPromptHeaderReject; apply execution; try reflexivity;
         auto using decodeItemInstalledBytes; lia]]
  end.

Lemma decodeItemLiteralSailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 -> decodeItemSailSuccess args false 0 1.
Proof. decodeItemSailBranch decodeItemLiteralCandidateIntro decodeItemRunPromptLiteralHeader. Qed.

Lemma decodeItemEmptySailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix = 128 -> decodeItemSailSuccess args false 1 0.
Proof.
  intros Hdomain Hinput Hclass.
  apply decodeItemSailSuccessFromPrompt; first exact Hdomain.
  unfold decodeItemInputHead in Hinput. unfold decodeItemSailCursor. rewrite Hinput.
  eapply decodeItemRunPromptAcceptedHeader; try reflexivity; try (simpl; lia).
  sail_eval.
Qed.

Lemma decodeItemShortStringSailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  1 + (bv_unsigned prefix - 128) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemSailSuccess args false 1 (bv_unsigned prefix - 128).
Proof. decodeItemSailBranch decodeItemShortStringCandidateIntro decodeItemRunPromptShortStringHeader. Qed.

Lemma decodeItemShortListSailSuccess args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  1 + (bv_unsigned prefix - 192) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemSailSuccess args true 1 (bv_unsigned prefix - 192).
Proof. decodeItemSailBranch decodeItemShortListCandidateIntro decodeItemRunPromptShortListHeader. Qed.

Print Assumptions decodeItemSailSuccessFromPrompt.
Print Assumptions decodeItemLiteralSailSuccess.
Print Assumptions decodeItemEmptySailSuccess.
Print Assumptions decodeItemShortStringSailSuccess.
Print Assumptions decodeItemShortListSailSuccess.

Lemma decodeItemLiteralAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix <= 127 -> decodeItemAcceptedFacts args false 0 1.
Proof. decodeItemSailBranch decodeItemLiteralCandidateIntro decodeItemLiteralSailSuccess. Qed.

Lemma decodeItemEmptyAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  bv_unsigned prefix = 128 -> decodeItemAcceptedFacts args false 1 0.
Proof. decodeItemSailBranch decodeItemEmptyCandidateIntro decodeItemEmptySailSuccess. Qed.

Lemma decodeItemShortStringAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  1 + (bv_unsigned prefix - 128) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128).
Proof. decodeItemSailBranch decodeItemShortStringCandidateIntro decodeItemShortStringSailSuccess. Qed.

Lemma decodeItemShortListAccepted args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  1 + (bv_unsigned prefix - 192) <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  decodeItemAcceptedFacts args true 1 (bv_unsigned prefix - 192).
Proof. decodeItemSailBranch decodeItemShortListCandidateIntro decodeItemShortListSailSuccess. Qed.

Print Assumptions decodeItemLiteralAccepted.
Print Assumptions decodeItemEmptyAccepted.
Print Assumptions decodeItemShortStringAccepted.
Print Assumptions decodeItemShortListAccepted.



Lemma decodeItemShortStringRejected args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  129 <= bv_unsigned prefix <= 183 ->
  Z.of_nat (List.length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 128) ->
  decodeItemRejectedFacts args.
Proof. decodeItemSailBranch decodeItemShortStringRejectedCandidateIntro decodeItemRunPromptShortStringHeader. Qed.

Lemma decodeItemShortListRejected args prefix rest :
  decodeItemC1BDomain args -> decodeItemInputHead args prefix rest ->
  192 <= bv_unsigned prefix <= 247 ->
  Z.of_nat (List.length (decodeItemInputBytes args)) < 1 + (bv_unsigned prefix - 192) ->
  decodeItemRejectedFacts args.
Proof. decodeItemSailBranch decodeItemShortListRejectedCandidateIntro decodeItemRunPromptShortListHeader. Qed.

Print Assumptions decodeItemSailRejectFromPrompt.
Print Assumptions decodeItemShortStringRejected.
Print Assumptions decodeItemShortListRejected.
End PortedSailIntroduction.

(* Verbatim copy of ZesuSsz/Compliance/DecodeItemPathAgreement.v. *)
Module PortedPathAgreement.
Import ZesuSsz.Automation.Hooks.
From Coq Require Import Lia List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Import ListNotations.
Open Scope Z_scope.

(* Each success observation names the fixed SailRun evaluator on the same
   bytes as the machine result. The field metadata must match the return. *)
Definition decodeItemSailSuccess :=
  ZesuSsz.Contracts.DecodeItemReturnFacts.decodeItemSailSuccess.

Lemma decodeItemDomainInputFits args :
  decodeItemC1BDomain args ->
  inputAddressFits (decodeItemInputPointer args) (decodeItemInputBytes args).
Proof.
  intros [Hlength [_ Hlayout]].
  unfold decodeItemEntryLayout in Hlayout.
  destruct Hlayout as [Hnonnegative [_ [Hend _]]].
  unfold inputAddressFits. rewrite <- Hlength. auto.
Qed.

Lemma decodeItemSuccessAgreement args after isList headerLength payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList headerLength payloadLength) ->
  0 <= headerLength -> 0 <= payloadLength ->
  headerLength + payloadLength < word64Modulus ->
  decodeItemSailSuccess args isList headerLength payloadLength ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Himage Hheader Hpayload Hfits Hsail.
  unfold DecodeMeaningModuloKnownBugs. split.
  - unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult.
    split; [now apply decodeItemDomainInputFits|].
    split.
    + unfold candidateResult40. rewrite Hcandidate.
      unfold encodeResult in Himage.
      destruct Himage as [pad17 [pad34 [_ [_ [_ [_ [_ [_ Hresult]]]]]]]].
      exact Hresult.
    + rewrite Hcandidate. left. unfold noWrapConsumed.
      repeat split; try lia; apply Z.mod_small; lia.
  - left. unfold decodeItemSailResult.
    destruct Hsail as [fullLength [contentLength [field
      [Hrun [Hlist [Hlength Hcontent]]]]]].
    rewrite Hrun. unfold relateItem. simpl.
    rewrite Hlist, Hlength, Hcontent. exact Himage.
Qed.

Lemma decodeItemWrapAgreement args after isList headerLength payloadLength :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList headerLength payloadLength) ->
  binaryWrapCase headerLength payloadLength
    ((headerLength + payloadLength) mod word64Modulus) ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Himage Hwrap Hreject.
  unfold DecodeMeaningModuloKnownBugs. split.
  - unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult.
    split; [now apply decodeItemDomainInputFits|].
    split.
    + unfold candidateResult40. rewrite Hcandidate.
      unfold encodeResult in Himage.
      destruct Himage as [pad17 [pad34 [_ [_ [_ [_ [_ [_ Hresult]]]]]]]].
      exact Hresult.
    + rewrite Hcandidate. right. exact Hwrap.
  - right. exists RlpLongLengthWrap. split; [simpl; auto|].
    unfold decodeItemBugApplies. exists isList, headerLength, payloadLength.
    split; [exact Hcandidate|]. split; [exact Hwrap|].
    split; [|exact Hreject].
    unfold candidateResult40. rewrite Hcandidate.
    unfold encodeResult in Himage.
    destruct Himage as [pad17 [pad34 [_ [_ [_ [_ [_ [_ Hresult]]]]]]]].
    exact Hresult.
Qed.

Lemma decodeItemRejectAgreement args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError ->
  errorResult40 after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Hresult Himage Hreject.
  unfold DecodeMeaningModuloKnownBugs. split.
  - unfold decodeItemAllowsC1B, decodeItemAllows, C1BResult.
    split; [now apply decodeItemDomainInputFits|].
    split; [unfold candidateResult40; now rewrite Hcandidate|].
    now rewrite Hcandidate.
  - left. unfold decodeItemSailResult. rewrite Hreject.
    unfold relateItem. exact Himage.
Qed.

(* 0x800d69a0 has two incoming success classes. *)
Lemma decodeItemLiteralReturn args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 0 1 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
  decodeItemSailSuccess args false 0 1 ->
  DecodeMeaningModuloKnownBugs args after.
Proof. intros. eapply decodeItemSuccessAgreement; eauto; lia. Qed.

Lemma decodeItemClassShortReturn args after payloadLength (isList : bool) :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList 1 payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList 1 payloadLength) ->
  0 <= payloadLength -> 1 + payloadLength < word64Modulus ->
  decodeItemSailSuccess args isList 1 payloadLength ->
  DecodeMeaningModuloKnownBugs args after.
Proof. intros. eapply decodeItemSuccessAgreement; eauto; lia. Qed.

Definition decodeItemShortStringReturn args after payloadLength :=
  decodeItemClassShortReturn args after payloadLength false.

(* 0x800d69d4 returns the empty-string sentinel pointer. *)
Lemma decodeItemEmptyStringReturn args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 1 0 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
  decodeItemSailSuccess args false 1 0 ->
  DecodeMeaningModuloKnownBugs args after.
Proof. intros. eapply decodeItemSuccessAgreement; eauto; lia. Qed.

(* 0x800d6aa4 is the short-list return. *)
Definition decodeItemShortListReturn args after payloadLength :=
  decodeItemClassShortReturn args after payloadLength true.

(* 0x800d6a60 and 0x800d6b2c each allow the selected wrap bug. *)
Lemma decodeItemClassLongReturn args after headerLength payloadLength (isList : bool) :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) =
    candidateSuccess isList headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList headerLength payloadLength) ->
  (2 <= headerLength <= 9) -> 0 <= payloadLength ->
  ((headerLength + payloadLength < word64Modulus /\
    decodeItemSailSuccess args isList headerLength payloadLength) \/
   (binaryWrapCase headerLength payloadLength
      ((headerLength + payloadLength) mod word64Modulus) /\
    runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
      Reject RlpDecode)) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hcandidate Himage Hwidth Hpayload [[Hfits Hsail]|[Hwrap Hreject]].
  - eapply decodeItemSuccessAgreement; eauto; lia.
  - eapply decodeItemWrapAgreement; eauto.
Qed.

Definition decodeItemLongStringReturn args after headerLength payloadLength :=
  decodeItemClassLongReturn args after headerLength payloadLength false.

Definition decodeItemLongListReturn args after headerLength payloadLength :=
  decodeItemClassLongReturn args after headerLength payloadLength true.

(* 0x800d6b04 covers every rejected header or payload check. *)
Lemma decodeItemErrorReturn args after :
  decodeItemC1BDomain args ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateError ->
  errorResult40 after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args) =
    Reject RlpDecode ->
  DecodeMeaningModuloKnownBugs args after.
Proof. exact (decodeItemRejectAgreement args after). Qed.

(* Q23 pins these three eight-byte length wraps. The following computations
   check the concrete Sail action and candidate class, not an ELF execution. *)
Definition q23WrapStringPlusOne : list byte :=
  map (Z_to_bv 8) [191; 255; 255; 255; 255; 255; 255; 255; 248].

Definition q23WrapList : list byte :=
  map (Z_to_bv 8) [255; 255; 255; 255; 255; 255; 255; 255; 247].

Definition q23WrapCursor : RlpCursor 0 9 :=
  {| StatelessInputSliceFields_bytes := 0;
     StatelessInputSliceFields_len := 9 |}.

Lemma q23WrapCandidateClasses :
  candidateDecodeItem decodeItemWrapWitnessInput =
    candidateSuccess false 9 (word64Modulus - 9) /\
  candidateDecodeItem q23WrapStringPlusOne =
    candidateSuccess false 9 (word64Modulus - 8) /\
  candidateDecodeItem q23WrapList =
    candidateSuccess true 9 (word64Modulus - 9).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma q23WrapSailRejects :
  runRlpDecodeItem decodeItemWrapWitnessInput q23WrapCursor = Reject RlpDecode /\
  runRlpDecodeItem q23WrapStringPlusOne q23WrapCursor = Reject RlpDecode /\
  runRlpDecodeItem q23WrapList q23WrapCursor = Reject RlpDecode.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma q23LongStringWrapMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemInputBytes args = decodeItemWrapWitnessInput ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess false 9 (word64Modulus - 9)) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain Hbytes Himage.
  eapply decodeItemWrapAgreement; [exact Hdomain| |exact Himage| |].
  - rewrite Hbytes. exact (proj1 q23WrapCandidateClasses).
  - exact (proj1 (proj2 decodeItemWrapWitness)).
  - unfold decodeItemSailCursor. rewrite Hbytes.
    exact (proj1 q23WrapSailRejects).
Qed.
End PortedPathAgreement.

(* Verbatim copy of ZesuSsz/Compliance/DecodeItemReturnExitResources.v. *)
Module PortedReturnExitResources.
Import ZesuSsz.Automation.Hooks.
From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Import PortedPathAgreement.
Open Scope Z_scope.

(* These compositions use the S1 semantic facts and the exact output image.
   They supply no instruction execution assumption. *)
Lemma decodeItemLiteralPostMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemAcceptedFacts args false 0 1 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 0 1) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hsail] Himage.
  eapply decodeItemLiteralReturn; eauto.
Qed.

Lemma decodeItemEmptyStringPostMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemAcceptedFacts args false 1 0 ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after (candidateSuccess false 1 0) ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hsail] Himage.
  eapply decodeItemEmptyStringReturn; eauto.
Qed.

Lemma decodeItemClassShortPostMeaning args after payloadLength (isList : bool) :
  decodeItemC1BDomain args ->
  decodeItemAcceptedFacts args isList 1 payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList 1 payloadLength) ->
  0 <= payloadLength -> 1 + payloadLength < word64Modulus ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hsail] Himage Hnonnegative Hbound.
  eapply decodeItemClassShortReturn; eauto.
Qed.

Definition decodeItemShortStringPostMeaning args after payloadLength :=
  decodeItemClassShortPostMeaning args after payloadLength false.

Definition decodeItemShortListPostMeaning args after payloadLength :=
  decodeItemClassShortPostMeaning args after payloadLength true.

Lemma decodeItemClassLongPostMeaning args after headerLength payloadLength (isList : bool) :
  decodeItemC1BDomain args ->
  decodeItemLongAcceptedFacts args isList headerLength payloadLength ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after
    (candidateSuccess isList headerLength payloadLength) ->
  2 <= headerLength <= 9 -> 0 <= payloadLength ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hpath] Himage Hwidth Hnonnegative.
  eapply decodeItemClassLongReturn; eauto.
Qed.

Definition decodeItemLongStringPostMeaning args after headerLength payloadLength :=
  decodeItemClassLongPostMeaning args after headerLength payloadLength false.

Definition decodeItemLongListPostMeaning args after headerLength payloadLength :=
  decodeItemClassLongPostMeaning args after headerLength payloadLength true.

Lemma decodeItemErrorPostMeaning args after :
  decodeItemC1BDomain args ->
  decodeItemRejectedFacts args ->
  errorResult40 after ->
  encodeResult (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after candidateError ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros Hdomain [Hcandidate Hreject] Herror Himage.
  eapply decodeItemErrorReturn; eauto.
Qed.
End PortedReturnExitResources.

(* Verbatim copy of ZesuSsz/Compliance/DecodeItemReturnExitPure.v. *)
Module PortedReturnExitPure.
Import ZesuSsz.Automation.Hooks.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Import PortedReturnImages.
Require Import ZesuSsz.Compliance.SailRun.
Import PortedPathAgreement.
Import ListNotations.
Open Scope Z_scope.

(* Each lemma connects an exact Q44 byte image to the Q45 path fact.
   Machine ownership and writes at these PCs remain block obligations. *)


Lemma returnExitEmptyString args prefix rest pointerBytes lengthBytes consumedBytes :
  decodeItemInputBytes args = prefix :: rest ->
  decodeItemC1BDomain args ->
  bv_unsigned prefix = 128 ->
  (length (decodeItemBeforeStorage args) = 40)%nat ->
  (length pointerBytes = 8)%nat ->
  (length lengthBytes = 8)%nat ->
  (length consumedBytes = 8)%nat ->
  littleEndian pointerBytes = 1 ->
  littleEndian lengthBytes = 0 ->
  littleEndian consumedBytes = 1 mod word64Modulus ->
  candidateDecodeItem (decodeItemInputBytes args) = candidateSuccess false 1 0 ->
  decodeItemSailSuccess args false 1 0 ->
  DecodeMeaningModuloKnownBugs args
    (decodeItemOkBytes (decodeItemBeforeStorage args)
       pointerBytes lengthBytes consumedBytes false).
Proof.
  intros Hinput Hdomain Hprefix Hbefore Hp Hl Hc Hpv Hlv Hcv Hcandidate Hsail.
  eapply decodeItemEmptyStringReturn; [exact Hdomain|exact Hcandidate| |exact Hsail].
  rewrite Hinput. eapply return_800d69d4_emptyString; eauto.
Qed.
End PortedReturnExitPure.

Export PortedReturnImages.
Export PortedSemanticIntroduction.
Export PortedSailEvaluation.
Export PortedSailIntroduction.
Export PortedPathAgreement.
Export PortedReturnExitResources.
Export PortedReturnExitPure.
