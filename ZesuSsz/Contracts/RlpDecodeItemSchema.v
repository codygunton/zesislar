From Coq Require Import Lia List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord SailStdpp.Values.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Import ListNotations.
Open Scope Z_scope.

(* Stock ELF e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95.
   At 0x800d69b4 the 0x80 branch sets the payload pointer to 1.
   Other success branches use the input pointer plus the header length.
   Neither branch grants a points-to resource for the payload pointer. *)
Definition itemPayloadPointer (inputPointer : Z) (input : list byte)
    (headerLength : Z) : Z :=
  match input with
  | prefix :: _ => if bv_unsigned prefix =? 128 then 1
                   else inputPointer + headerLength
  | [] => inputPointer + headerLength
  end.

Definition errorEncoding : list byte :=
  List.repeat (mword_of_int 0) 32 ++ [mword_of_int 4] ++
  List.repeat (mword_of_int 0) 7.

(* The two witnesses are the unchanged bytes in [17,24) and [34,40).
   The entry resource can own them, or quantify them if storage is fresh. *)
Definition encodeResult (inputPointer : Z) (input before after : list byte)
    (result : candidateItem) : Prop :=
  match result with
  | candidateError => after = errorEncoding
  | candidateSuccess isList headerLength payloadLength =>
      exists pad17 pad34 : list byte,
        (length pad17 = 7)%nat /\ (length pad34 = 6)%nat /\
        pad17 = firstn 7 (skipn 17 before) /\
        pad34 = firstn 6 (skipn 34 before) /\
        pad17 = firstn 7 (skipn 17 after) /\
        pad34 = firstn 6 (skipn 34 after) /\
        successResult40 before after
          (itemPayloadPointer inputPointer input headerLength)
          payloadLength isList
          ((headerLength + payloadLength) mod word64Modulus)
  end.

Definition SailItemOutcome (base len : Z) : Type :=
  SailOutcome
    ({full_len & {content_len & RlpFieldRef base full_len content_len}}%type).

(* Sail gives a full item length and a content length. Their difference is
   the header length. A rejected Sail item maps to the complete error image. *)
Definition relateItem {base len : Z} (inputPointer : Z)
    (input before after : list byte) (outcome : SailItemOutcome base len)
    : Prop :=
  match outcome with
  | Success (existT full_len (existT content_len field)) =>
      encodeResult inputPointer input before after
        (candidateSuccess field.(RlpFieldRef_is_list)
          (full_len - content_len) content_len)
  | Reject RlpDecode => encodeResult inputPointer input before after candidateError
  | _ => False
  end.

(* This class requires enough bytes for every header and payload.
   It excludes the length-header arithmetic wrap without using headerFits. *)
Definition shortRlpPayloadLength (prefix : Z) : Z :=
  if prefix <? 128 then 0
  else if prefix <=? 183 then prefix - 128
  else if prefix <=? 247 then prefix - 192
  else 0.

Definition intendedValidRlpClass (input : list byte) : Prop :=
  match input with
  | [] => False
  | prefix :: rest =>
      Z.of_nat (length input) < word64Modulus /\
      let width := longLengthWidth (bv_unsigned prefix) in
      (width = 0 /\
       shortRlpPayloadLength (bv_unsigned prefix) <=
         Z.of_nat (length rest)) \/
      (0 < width /\ width <= Z.of_nat (length rest) /\
       1 + width + bigEndian (firstn (Z.to_nat width) rest) <=
         Z.of_nat (length input))
  end.

Lemma intendedValidRlpClassHeaderFits input :
  intendedValidRlpClass input -> headerFits input.
Proof.
  destruct input as [|prefix rest]; simpl; [tauto|].
  unfold intendedValidRlpClass, headerFits; simpl.
  intros [Hlength [[Hwidth _] | [_ [_ Hfull]]]].
  - left. exact Hwidth.
  - right. right. eapply Z.le_lt_trans; eauto.
Qed.
