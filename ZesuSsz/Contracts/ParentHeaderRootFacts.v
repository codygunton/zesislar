From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ZiskRuntime.

Import ListNotations.
Open Scope Z_scope.

(* The selected service states memory and return behavior.
   It supplies no service correctness proof or execution premise. *)
Definition selectedMemcpy : ZiskMemcpyServiceContract :=
  ziskMemcpyContract 0x800e06c0.

(* ELF 0x800d5d68 passes 0x50 bytes to the memcpy tail at 0x800d5da0.
   The first 72 bytes hold ParentHeader. Bytes 72 and 73 hold the error tag.
   The remaining six bytes are padding and have no value requirement. *)
Definition parentHeaderResult80 (bytes : list byte)
    (value : ParentHeaderValue) : Prop :=
  List.length bytes = 80%nat /\
  parentHeaderResult72 (firstn 72 bytes) value /\
  byteAt bytes 72 0 /\ byteAt bytes 73 0.

(* The direct error path writes tag 3 at 0x800d5f28. The memcpy path
   copies a constant error union from 0x80114fb8. Its tag is also 3. *)
Definition parentHeaderError80 (bytes : list byte) : Prop :=
  List.length bytes = 80%nat /\
  byteAt bytes 72 3 /\ byteAt bytes 73 0.

Definition nextUint64StackBytes : Z := 96.
Definition parentHeaderStackBytes : Z := 400.
Definition parentHeaderTailPc : Z := 0x800d5da0.
Definition parentHeaderReturnPc : Z := 0x800d5f58.
Definition nextUint64ReturnPc : Z := 0x800d6300.

(* The CFG lists 17 direct decodeItem call sites. The first site decodes
   the outer header. The three nextUint64 sites also call decodeItem.
   A machine proof must connect each call to its actual a1/a2 slice.
   Nested length wraps use the same C1-B known-bug relation. *)
Definition parentHeaderDecodeItemCallSites : list Z :=
  [0x800d5cf4; 0x800d5d34; 0x800d5dbc; 0x800d5de8;
   0x800d5e14; 0x800d5e40; 0x800d5e6c; 0x800d5e98;
   0x800d5ec4; 0x800d5ef0; 0x800d5f18; 0x800d5fb4;
   0x800d601c; 0x800d60b4; 0x800d60ec; 0x800d6118;
   0x800d6198].

Definition parentHeaderNextUint64CallSites : list Z :=
  [0x800d615c; 0x800d621c; 0x800d6250].

Definition nestedC1AObligation
    (callInputAt : Z -> list byte -> Prop) : Prop :=
  forall pc bytes,
    List.In pc
      (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites) ->
    callInputAt pc bytes -> headerFits bytes.

Definition nextUint64EntryLayout (inputPointer inputLength slicePointer
    resultPointer stackPointer returnAddress : Z) : Prop :=
  0 <= inputPointer /\ 0 <= inputLength /\
  inputPointer + inputLength < word64Modulus /\
  0 <= slicePointer /\ slicePointer + 16 < word64Modulus /\
  0 <= resultPointer /\ resultPointer + 16 < word64Modulus /\
  nextUint64StackBytes <= stackPointer < word64Modulus /\
  separateRanges inputPointer inputLength resultPointer 16 /\
  separateRanges inputPointer inputLength
    (stackPointer - nextUint64StackBytes) nextUint64StackBytes /\
  separateRanges resultPointer 16
    (stackPointer - nextUint64StackBytes) nextUint64StackBytes /\
  separateRanges slicePointer 16 resultPointer 16 /\
  separateRanges slicePointer 16
    (stackPointer - nextUint64StackBytes) nextUint64StackBytes /\
  0 <= returnAddress < word64Modulus /\ returnAddress mod 4 = 0.

Definition parentHeaderEntryLayout (inputPointer inputLength resultPointer
    stackPointer returnAddress : Z) : Prop :=
  0 <= inputPointer /\ 0 <= inputLength /\
  inputPointer + inputLength < word64Modulus /\
  0 <= resultPointer /\ resultPointer + 80 < word64Modulus /\
  parentHeaderStackBytes <= stackPointer < word64Modulus /\
  separateRanges inputPointer inputLength resultPointer 80 /\
  separateRanges inputPointer inputLength
    (stackPointer - parentHeaderStackBytes) parentHeaderStackBytes /\
  separateRanges resultPointer 80
    (stackPointer - parentHeaderStackBytes) parentHeaderStackBytes /\
  0 <= returnAddress < word64Modulus /\ returnAddress mod 4 = 0.

(* The nextUint64 input is a two-word slice at a1. The result is 16 bytes
   at a0. On success, the input slice advances by the consumed item size.
   On failure, the input slice is not written. *)
Record NextUint64Call := {
  nextInputPointer : Z;
  nextInputBytes : list byte;
  nextSlicePointer : Z;
  nextResultPointer : Z;
  nextStackPointer : Z;
  nextReturnAddress : Z;
  nextSavedS0 : bv 64;
  nextSavedS1 : bv 64;
  nextSavedS2 : bv 64;
  nextSavedS3 : bv 64;
  nextSavedS4 : bv 64
}.

Record NextUint64Return := {
  nextResultBytes : list byte;
  nextRestPointer : Z;
  nextRestLength : Z
}.

Definition nextUint64RootResult (call : NextUint64Call)
    (ret : NextUint64Return) : Prop :=
  inputAddressFits call.(nextInputPointer) call.(nextInputBytes) /\
  match candidateDecodeItem call.(nextInputBytes) with
  | candidateError =>
      nextUint64Error16 ret.(nextResultBytes) /\
      ret.(nextRestPointer) = call.(nextInputPointer) /\
      ret.(nextRestLength) = Z.of_nat (List.length call.(nextInputBytes))
  | candidateSuccess isList headerLength payloadLength =>
      if isList || (8 <? payloadLength) then
        nextUint64Error16 ret.(nextResultBytes) /\
        ret.(nextRestPointer) = call.(nextInputPointer) /\
        ret.(nextRestLength) = Z.of_nat (List.length call.(nextInputBytes))
      else
        let consumed := headerLength + payloadLength in
        let payload := firstn (Z.to_nat payloadLength)
          (skipn (Z.to_nat headerLength) call.(nextInputBytes)) in
        nextUint64Success16 ret.(nextResultBytes) payload /\
        ret.(nextRestPointer) = call.(nextInputPointer) + consumed /\
        ret.(nextRestLength) =
          Z.of_nat (List.length call.(nextInputBytes)) - consumed
  end.
