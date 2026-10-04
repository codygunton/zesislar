From Coq Require Import Bool List ZArith.
Require Import SailStdpp.MachineWord.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.

Import ListNotations.
Open Scope Z_scope.

(* Pinned Zesu rlp_decode.zig:119-130 requires nine skipped fields,
   then gas_limit, gas_used, and timestamp as uint64 fields. The
   optional fields begin at rlp_decode.zig:132. This parser names a
   missing required field. Malformed or wrapped items are separate. *)
Inductive RequiredFieldScan :=
| RequiredPresent (remaining : list byte)
| RequiredMissing
| RequiredInvalid.

Definition requiredItemWithin (remaining : list byte)
    (headerLength payloadLength : Z) : bool :=
  (0 <? headerLength + payloadLength) &&
  (headerLength + payloadLength <=? Z.of_nat (List.length remaining)).

Fixpoint scanRequiredFields (kinds : list bool)
    (remaining : list byte) : RequiredFieldScan :=
  match kinds with
  | [] => RequiredPresent remaining
  | isInteger :: later =>
      match remaining with
      | [] => RequiredMissing
      | _ =>
          match candidateDecodeItem remaining with
          | candidateError => RequiredInvalid
          | candidateSuccess isList headerLength payloadLength =>
              if requiredItemWithin remaining headerLength payloadLength &&
                 (negb isInteger || (negb isList && (payloadLength <=? 8)))
              then scanRequiredFields later
                (skipn (Z.to_nat (headerLength + payloadLength)) remaining)
              else RequiredInvalid
          end
      end
  end.

Definition requiredParentFields : list bool :=
  List.repeat false 9 ++ List.repeat true 3.

Definition parentHeaderRequiredScan (bytes : list byte) : RequiredFieldScan :=
  match candidateDecodeItem bytes with
  | candidateError => RequiredInvalid
  | candidateSuccess isList headerLength payloadLength =>
      if isList && requiredItemWithin bytes headerLength payloadLength
      then scanRequiredFields requiredParentFields
        (firstn (Z.to_nat payloadLength)
          (skipn (Z.to_nat headerLength) bytes))
      else RequiredInvalid
  end.

Definition parentHeaderMissingRequiredField (bytes : list byte) : Prop :=
  parentHeaderRequiredScan bytes = RequiredMissing.

Example emptyParentListMissesRequired :
  parentHeaderMissingRequiredField [Z_to_bv 8 192].
Proof. vm_compute. reflexivity. Qed.

Example twelveEmptyFieldsSatisfyRequired :
  ~ parentHeaderMissingRequiredField
      (Z_to_bv 8 204 :: List.repeat (Z_to_bv 8 128) 12).
Proof. vm_compute. discriminate. Qed.
