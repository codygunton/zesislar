From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Import ListNotations.
Open Scope Z_scope.

Record NextUint64Args := {
  nextUint64Base : NextUint64Call;
  nextUint64InputEnd : Z;
  nextUint64SavedX21 : bv 64; nextUint64SavedX22 : bv 64;
  nextUint64SavedX23 : bv 64; nextUint64SavedX24 : bv 64;
  nextUint64SavedX25 : bv 64; nextUint64SavedX26 : bv 64;
  nextUint64SavedX27 : bv 64
}.

(* The caller subtracts 96. Its separate callee frame has 16 bytes. *)
Definition nextUint64BoundaryDomain (params : NextUint64Args) : Prop :=
  let args := nextUint64Base params in
  let inputLength := Z.of_nat (length (nextInputBytes args)) in
  nextUint64EntryLayout (nextInputPointer args) inputLength
    (nextSlicePointer args) (nextResultPointer args)
    (nextStackPointer args) (nextReturnAddress args) /\
  112 <= nextStackPointer args /\
  0 <= nextUint64InputEnd params < word64Modulus /\
  nextInputPointer args + inputLength <= nextUint64InputEnd params /\
  decodeItemEntryLayout (nextInputPointer args) inputLength
    (nextStackPointer args - 88) (nextStackPointer args - 96)
    0x800d62b8 (nextUint64InputEnd params) /\
  separateRanges (nextInputPointer args) inputLength
    (nextStackPointer args - 112) 112 /\
  separateRanges (nextSlicePointer args) 16 (nextStackPointer args - 112) 112 /\
  separateRanges (nextResultPointer args) 16 (nextStackPointer args - 112) 112.

Definition nextUint64CalleeBase (params : NextUint64Args)
    (before : list byte) : DecodeItemArgs :=
  let args := nextUint64Base params in
  {| decodeItemOutputPointer := nextStackPointer args - 88;
     decodeItemInputPointer := nextInputPointer args;
     decodeItemInputLength := Z.of_nat (length (nextInputBytes args));
     decodeItemInputBytes := nextInputBytes args;
     decodeItemBeforeStorage := before;
     decodeItemStackPointer := nextStackPointer args - 96;
     decodeItemReturnAddress := 0x800d62b8;
     decodeItemSavedFramePointer := Z_to_bv 64 (nextStackPointer args);
     decodeItemInputEnd := nextUint64InputEnd params |}.

Definition nextUint64SysRegs (params : NextUint64Args) :=
  decodeItemSysRegs (nextUint64CalleeBase params []).

Definition nextUint64SliceImage (pointer length : Z) : list byte :=
  word64Bytes pointer ++ word64Bytes length.

Definition nextUint64DecodedPointer (decoded : list byte) : Z :=
  littleEndian (firstn 8 decoded).
Definition nextUint64DecodedLength (decoded : list byte) : Z :=
  littleEndian (firstn 8 (skipn 8 decoded)).
Definition nextUint64DecodedConsumed (decoded : list byte) : Z :=
  littleEndian (firstn 8 (skipn 24 decoded)).
Definition nextUint64DecodedStatus (decoded : list byte) : Z :=
  littleEndian (firstn 2 (skipn 32 decoded)).
Definition nextUint64DecodedTag (decoded : list byte) : Z :=
  littleEndian (firstn 1 (skipn 16 decoded)).

Definition nextUint64DecodedFacts (params : NextUint64Args)
    (decoded : list byte) : Prop :=
  exists before : list byte,
    length before = 40%nat /\
    DecodeMeaningModuloKnownBugs (nextUint64CalleeBase params before) decoded.

Definition nextUint64Rejects (args : NextUint64Call) : Prop :=
  match candidateDecodeItem (nextInputBytes args) with
  | candidateError => True
  | candidateSuccess isList _ payloadLength =>
      isList = true \/ 8 < payloadLength
  end.

Definition nextUint64AcceptedBytes (args : NextUint64Call)
    (decoded : list byte) : Prop :=
  exists headerLength payloadLength,
    candidateDecodeItem (nextInputBytes args) =
      candidateSuccess false headerLength payloadLength /\
    0 <= headerLength /\ 0 <= payloadLength <= 8 /\
    headerLength + payloadLength <= Z.of_nat (length (nextInputBytes args)) /\
    length decoded = 40%nat /\
    nextUint64DecodedPointer decoded = nextInputPointer args + headerLength /\
    nextUint64DecodedLength decoded = payloadLength /\
    nextUint64DecodedConsumed decoded = headerLength + payloadLength /\
    byteAt decoded 16 0 /\ byteAt decoded 32 0 /\ byteAt decoded 33 0.

Definition nextUint64Payload (args : NextUint64Call)
    (decoded : list byte) : list byte :=
  firstn (Z.to_nat (nextUint64DecodedLength decoded))
    (skipn (Z.to_nat (nextUint64DecodedPointer decoded - nextInputPointer args))
      (nextInputBytes args)).

Definition nextUint64FoldInvariant (args : NextUint64Call)
    (decoded : list byte) (current limit accumulator : bv 64) : Prop :=
  let payloadStart := nextUint64DecodedPointer decoded in
  let payloadLength := nextUint64DecodedLength decoded in
  exists cursor : Z,
    bv_unsigned current = cursor /\
    nextUint64AcceptedBytes args decoded /\
    payloadLength <> 0 /\
    0 <= cursor - payloadStart < payloadLength /\
    bv_unsigned limit = payloadStart + payloadLength /\
    0 <= payloadStart /\ payloadStart + payloadLength < word64Modulus /\
    Z.of_nat (length (nextUint64Payload args decoded)) = payloadLength /\
    bv_unsigned accumulator = bigEndian
      (firstn (Z.to_nat (cursor - payloadStart)) (nextUint64Payload args decoded)).

Definition nextUint64FoldComplete (args : NextUint64Call)
    (decoded : list byte) (accumulator : bv 64) : Prop :=
  nextUint64AcceptedBytes args decoded /\
  bv_unsigned accumulator = bigEndian (nextUint64Payload args decoded).

Definition nextUint64SavedFrameFacts (args : NextUint64Call)
    (saved : list byte) : Prop :=
  length saved = 48%nat /\
  word64At saved 0 (bv_unsigned (nextSavedS4 args)) /\
  word64At saved 8 (bv_unsigned (nextSavedS3 args)) /\
  word64At saved 16 (bv_unsigned (nextSavedS2 args)) /\
  word64At saved 24 (bv_unsigned (nextSavedS1 args)) /\
  word64At saved 32 (bv_unsigned (nextSavedS0 args)) /\
  word64At saved 40 (nextReturnAddress args).

Definition nextUint64Registers `{!islaG Sigma} `{!threadG}
    (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits x1 ∗
   "x2" ↦ᵣ RVal_Bits x2 ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗
   "x6" ↦ᵣ RVal_Bits x6 ∗
   "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits x8 ∗
   "x9" ↦ᵣ RVal_Bits x9 ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗
   "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits x18 ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x20" ↦ᵣ RVal_Bits x20 ∗
   "x21" ↦ᵣ RVal_Bits x21 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗
   "x23" ↦ᵣ RVal_Bits x23 ∗
   "x24" ↦ᵣ RVal_Bits x24 ∗
   "x25" ↦ᵣ RVal_Bits x25 ∗
   "x26" ↦ᵣ RVal_Bits x26 ∗
   "x27" ↦ᵣ RVal_Bits x27 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗
   "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗
   "x31" ↦ᵣ RVal_Bits x31)%I.

Definition nextUint64PostMemory `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (nextInputPointer args ↦ₘ∗ inputBytes ∗
   nextSlicePointer args ↦ₘ∗ sliceBytes ∗
   (nextStackPointer args - 96) ↦ₘ? 8 ∗
   (nextStackPointer args - 88) ↦ₘ∗ decoded ∗
   (nextStackPointer args - 48) ↦ₘ∗ saved ∗
   (nextStackPointer args - 112) ↦ₘ? 16)%I.

Definition nextUint64PostFacts (params : NextUint64Args)
    (x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : bv 64)
    (inputBytes decoded saved : list byte) : Prop :=
  let args := nextUint64Base params in
  nextUint64BoundaryDomain params /\ inputBytes = nextInputBytes args /\
  length decoded = 40%nat /\ nextUint64SavedFrameFacts args saved /\
  x1 = Z_to_bv 64 0x800d62b8 /\
  x2 = Z_to_bv 64 (nextStackPointer args - 96) /\
  x8 = Z_to_bv 64 (nextStackPointer args) /\
  x9 = Z_to_bv 64 (nextResultPointer args) /\
  x18 = Z_to_bv 64 (nextSlicePointer args) /\
  x20 = Z_to_bv 64 (Z.of_nat (length (nextInputBytes args))) /\
  x21 = nextUint64SavedX21 params /\
  x22 = nextUint64SavedX22 params /\
  x23 = nextUint64SavedX23 params /\
  x24 = nextUint64SavedX24 params /\
  x25 = nextUint64SavedX25 params /\
  x26 = nextUint64SavedX26 params /\
  x27 = nextUint64SavedX27 params.

Definition nextUint64EntryAt800d6274 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextInputPointer args ↦ₘ∗ inputBytes ∗
   nextSlicePointer args ↦ₘ∗ sliceBytes ∗
   nextResultPointer args ↦ₘ? 16 ∗
   (nextStackPointer args - 96) ↦ₘ? 96 ∗
   (nextStackPointer args - 112) ↦ₘ? 16 ∗
   ⌜nextUint64BoundaryDomain params /\
     inputBytes = nextInputBytes args /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     x1 = Z_to_bv 64 (nextReturnAddress args) /\
     x2 = Z_to_bv 64 (nextStackPointer args) /\
     x8 = nextSavedS0 args /\
     x9 = nextSavedS1 args /\
     x10 = Z_to_bv 64 (nextResultPointer args) /\
     x11 = Z_to_bv 64 (nextSlicePointer args) /\
     x18 = nextSavedS2 args /\
     x19 = nextSavedS3 args /\
     x20 = nextSavedS4 args /\
     x21 = nextUint64SavedX21 params /\
     x22 = nextUint64SavedX22 params /\
     x23 = nextUint64SavedX23 params /\
     x24 = nextUint64SavedX24 params /\
     x25 = nextUint64SavedX25 params /\
     x26 = nextUint64SavedX26 params /\
     x27 = nextUint64SavedX27 params⌝ ∗ True)%I.

Definition nextUint64EntryAt800d62b8 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64DecodedFacts params decoded⌝ ∗ True)%I.

Definition nextUint64EntryAt800d62c0 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64DecodedFacts params decoded /\
     nextUint64DecodedStatus decoded = 0 /\
     x10 = Z_to_bv 64 0⌝ ∗ True)%I.

Definition nextUint64EntryAt800d62cc `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64DecodedFacts params decoded /\
     nextUint64DecodedStatus decoded = 0 /\
     Z.land (nextUint64DecodedTag decoded) 1 = 0 /\
     x10 = Z_to_bv 64 0⌝ ∗ True)%I.

Definition nextUint64EntryAt800d62d8 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64Rejects args⌝ ∗ True)%I.

Definition nextUint64EntryAt800d62e4 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved resultBytes : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ∗ resultBytes ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     exists result : NextUint64Return, nextResultBytes result = resultBytes /\ nextUint64RootResult args result /\ sliceBytes = nextUint64SliceImage (nextRestPointer result) (nextRestLength result) /\
     length resultBytes = 16%nat /\
     bv_unsigned x19 = littleEndian (firstn 8 sliceBytes)⌝ ∗ True)%I.

Definition nextUint64EntryAt800d6304 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64AcceptedBytes args decoded /\
     bv_unsigned x13 = nextUint64DecodedLength decoded /\
     x10 = Z_to_bv 64 8⌝ ∗ True)%I.

Definition nextUint64EntryAt800d6310 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64AcceptedBytes args decoded /\
     nextUint64DecodedLength decoded <> 0 /\
     bv_unsigned x13 = nextUint64DecodedLength decoded /\
     bv_unsigned x10 = nextUint64DecodedConsumed decoded /\
     x11 = Z_to_bv 64 0⌝ ∗ True)%I.

Definition nextUint64EntryAt800d6318 `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64FoldInvariant args decoded x12 x13 x11 /\
     bv_unsigned x10 = nextUint64DecodedConsumed decoded⌝ ∗ True)%I.

Definition nextUint64EntryAt800d632c `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64)
    (inputBytes sliceBytes decoded saved : list byte) : iProp Sigma :=
  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64FoldComplete args decoded x11 /\
     bv_unsigned x10 = nextUint64DecodedConsumed decoded⌝ ∗ True)%I.

Definition nextUint64BoundaryEntry `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) : iProp Sigma :=
  let args := nextUint64Base params in
  (∃ x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64,
   nextUint64EntryAt800d6274 params
     (Z_to_bv 64 (nextReturnAddress args)) (Z_to_bv 64 (nextStackPointer args)) x5 x6 x7 (nextSavedS0 args) (nextSavedS1 args) x10 x11 x12 x13 x14 x15 x16 x17 (nextSavedS2 args) (nextSavedS3 args) (nextSavedS4 args) (nextUint64SavedX21 params) (nextUint64SavedX22 params) (nextUint64SavedX23 params) (nextUint64SavedX24 params) (nextUint64SavedX25 params) (nextUint64SavedX26 params) (nextUint64SavedX27 params) x28 x29 x30 x31
     (nextInputBytes args) (nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args)))))%I.
