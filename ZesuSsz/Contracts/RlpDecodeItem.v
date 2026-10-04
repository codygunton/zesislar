From Coq Require Import List String ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Import ListNotations.
Open Scope Z_scope.

(* The selected stock ELF is build/stock-zisk/zesu-zisk.elf. *)
Definition decodeItemElfSha256 : string :=
  "e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95"%string.
Definition decodeItemEntry : Z := 0x800d6960.
Definition decodeItemRegionEnd : Z := 0x800d6b30.
Definition decodeItemReturnSites : list Z :=
  [0x800d69a0; 0x800d69d4; 0x800d6a60;
   0x800d6aa4; 0x800d6b04; 0x800d6b2c].
Definition decodeItemStackBytes : Z := 16.
Definition word64Modulus : Z := 2 ^ 64.

(* The result owns 40 bytes. Success preserves the two padding ranges. *)
Fixpoint littleEndian (bytes : list byte) : Z :=
  match bytes with
  | [] => 0
  | b :: rest => bv_unsigned b + 256 * littleEndian rest
  end.

Definition word64At (bytes : list byte) (offset : nat) (value : Z) : Prop :=
  (List.length (firstn 8 (skipn offset bytes)) = 8)%nat /\
  littleEndian (firstn 8 (skipn offset bytes)) = value.

Definition byteAt (bytes : list byte) (offset : nat) (value : Z) : Prop :=
  option_map bv_unsigned (nth_error bytes offset) = Some value.

Definition successResult40 (before after : list byte)
    (payloadPointer payloadLength : Z) (isList : bool) (consumed : Z) : Prop :=
  (List.length before = 40)%nat /\ (List.length after = 40)%nat /\
  word64At after 0 payloadPointer /\
  word64At after 8 payloadLength /\
  byteAt after 16 (if isList then 1 else 0) /\
  word64At after 24 consumed /\
  byteAt after 32 0 /\ byteAt after 33 0 /\
  (forall i, (17 <= i < 24 \/ 34 <= i < 40)%nat ->
     nth_error after i = nth_error before i).

Definition errorResult40 (after : list byte) : Prop :=
  (List.length after = 40)%nat /\
  forall i, (i < 40)%nat -> byteAt after i (if Nat.eqb i 32 then 4 else 0).

(* RLP long strings use 0xb8..0xbf; long lists use 0xf8..0xff. *)
Definition longLengthWidth (prefix : Z) : Z :=
  if (184 <=? prefix) && (prefix <=? 191) then prefix - 183
  else if (248 <=? prefix) && (prefix <=? 255) then prefix - 247
  else 0.

Definition bigEndian (bytes : list byte) : Z :=
  List.fold_left (fun acc b => 256 * acc + bv_unsigned b) bytes 0.

(* A truncated length header remains in the domain because it rejects. *)
Definition headerFits (bytes : list byte) : Prop :=
  match bytes with
  | [] => True
  | prefix :: rest =>
      let width := longLengthWidth (bv_unsigned prefix) in
      width = 0 \/ Z.of_nat (List.length rest) < width \/
      1 + width + bigEndian (firstn (Z.to_nat width) rest) < word64Modulus
  end.

Definition inputAddressFits (inputPointer : Z) (bytes : list byte) : Prop :=
  0 <= inputPointer /\
  inputPointer + Z.of_nat (List.length bytes) < word64Modulus.

Definition separateRanges (first firstLength second secondLength : Z) : Prop :=
  first + firstLength <= second \/ second + secondLength <= first.

(* These address facts accompany the Level 1 input, result, stack, and
   continuation resources. The resource ownership remains a proof obligation. *)
Definition decodeItemEntryLayout (inputPointer inputLength resultPointer
    stackPointer returnAddress : Z) : Prop :=
  0 <= inputPointer /\ 0 <= inputLength /\
  inputPointer + inputLength < word64Modulus /\
  0 <= resultPointer /\ resultPointer + 40 < word64Modulus /\
  decodeItemStackBytes <= stackPointer < word64Modulus /\
  separateRanges inputPointer inputLength resultPointer 40 /\
  separateRanges inputPointer inputLength
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  separateRanges resultPointer 40
    (stackPointer - decodeItemStackBytes) decodeItemStackBytes /\
  0 <= returnAddress < word64Modulus /\ returnAddress mod 4 = 0.

Definition noWrapConsumed (headerLength payloadLength consumed : Z) : Prop :=
  0 <= headerLength /\ 0 <= payloadLength /\
  headerLength + payloadLength < word64Modulus /\
  consumed = headerLength + payloadLength.

Definition binaryWrapCase (headerLength payloadLength consumed : Z) : Prop :=
  0 <= headerLength /\ 0 <= payloadLength /\
  word64Modulus <= headerLength + payloadLength /\
  consumed = (headerLength + payloadLength) mod word64Modulus.

Inductive candidateItem : Type :=
| candidateError
| candidateSuccess (isList : bool) (headerLength payloadLength : Z).

Definition checkedPayload (inputLength headerLength payloadLength : Z)
    (isList : bool) : candidateItem :=
  if (headerLength + payloadLength) mod word64Modulus <=? inputLength
  then candidateSuccess isList headerLength payloadLength
  else candidateError.

(* This candidate follows the selected code's six return classes. A Level 1
   proof must establish its correspondence with the ELF. It is not evidence. *)
Definition candidateDecodeItem (input : list byte) : candidateItem :=
  match input with
  | [] => candidateError
  | prefix :: rest =>
      let first := bv_unsigned prefix in
      let inputLength := Z.of_nat (List.length input) in
      if first <=? 127 then candidateSuccess false 0 1
      else if first =? 128 then candidateSuccess false 1 0
      else if first <=? 183 then
        checkedPayload inputLength 1 (first - 128) false
      else if first <=? 191 then
        let width := first - 183 in
        if 1 + width <=? inputLength then
          checkedPayload inputLength (1 + width)
            (bigEndian (firstn (Z.to_nat width) rest)) false
        else candidateError
      else if first <=? 247 then
        checkedPayload inputLength 1 (first - 192) true
      else
        let width := first - 247 in
        if 1 + width <=? inputLength then
          checkedPayload inputLength (1 + width)
            (bigEndian (firstn (Z.to_nat width) rest)) true
        else candidateError
  end.

Definition candidateResult40 (inputPointer : Z) (input before after : list byte)
    : Prop :=
  match candidateDecodeItem input with
  | candidateError => errorResult40 after
  | candidateSuccess isList headerLength payloadLength =>
      let payloadPointer :=
        match input with
        | prefix :: _ => if bv_unsigned prefix =? 128 then 1
                         else inputPointer + headerLength
        | [] => inputPointer + headerLength
        end in
      successResult40 before after payloadPointer payloadLength isList
        ((headerLength + payloadLength) mod word64Modulus)
  end.

(* C1-B keeps the wrap result and states its arithmetic case explicitly.
   A wrap result does not grant ownership of its claimed payload range. *)
Definition C1BResult (inputPointer : Z) (input before after : list byte) : Prop :=
  inputAddressFits inputPointer input /\
  candidateResult40 inputPointer input before after /\
  match candidateDecodeItem input with
  | candidateError => True
  | candidateSuccess _ headerLength payloadLength =>
      let consumed := (headerLength + payloadLength) mod word64Modulus in
      noWrapConsumed headerLength payloadLength consumed \/
      binaryWrapCase headerLength payloadLength consumed
  end.
