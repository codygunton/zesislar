From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.DomainRanges.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* Shared statements of the std.ArrayListAligned regions reached from
   rlp_decode.txAccessList, for element types [32]u8 (keys) and
   input.AccessListEntry (entries). An array list is the 24-byte header
   {items.ptr, items.len, capacity}; its buffer is an allocator block of
   capacity * elementBytes bytes whose first length * elementBytes bytes are
   the items. The allocator is alt_fl_alloc (AltFlAllocPremises.v). *)

Notation keysElementBytes := ((32) : Z) (only parsing).
Notation keysLog2Alignment := ((0) : Z) (only parsing).
Notation keysEmptyPointer := ((1) : Z) (only parsing).
Notation entriesElementBytes := ((40) : Z) (only parsing).
Notation entriesLog2Alignment := ((3) : Z) (only parsing).
Notation entriesEmptyPointer := ((8) : Z) (only parsing).

Notation arrayListHeaderSize := ((24) : Z) (only parsing).
Notation arrayListResultSize := ((24) : Z) (only parsing).
Notation arrayListAllocatorSize := ((16) : Z) (only parsing).
Notation arrayListOutOfMemoryCode := ((2) : Z) (only parsing).
(* Own frame 96 bytes, plus the 16-byte frame of an allocator callee. *)
Notation arrayListToOwnedSliceStackBytes := ((96 + 16) : Z) (only parsing).

Record ArrayListState : Type := {
  arrayListPointer : Z;
  arrayListLength : Z;
  arrayListCapacity : Z;
  arrayListItems : list byte
}.

Definition arrayListEmpty (pointer : Z) : ArrayListState :=
  {| arrayListPointer := pointer; arrayListLength := 0;
     arrayListCapacity := 0; arrayListItems := [] |}.

Definition arrayListHeaderBytes (state : ArrayListState) : list byte :=
  word64Bytes (arrayListPointer state) ++ word64Bytes (arrayListLength state) ++
  word64Bytes (arrayListCapacity state).

Definition arrayListRamRange (pointer bytes : Z) : Prop :=
  mapRamBase defaultMap <= pointer /\ pointer + bytes <= machineRamEnd defaultMap.

(* items.ptr is a non-null Zig pointer; a list with capacity has its buffer
   in RAM. *)
Definition arrayListWellFormed (elementBytes : Z) (state : ArrayListState) : Prop :=
  0 <= arrayListLength state <= arrayListCapacity state /\
  Z.of_nat (length (arrayListItems state)) = arrayListLength state * elementBytes /\
  0 < arrayListPointer state < 2 ^ 64 /\
  (0 < arrayListCapacity state ->
    arrayListRamRange (arrayListPointer state)
      (arrayListCapacity state * elementBytes)).

(* The buffer: the items, the unused capacity, and the allocator token. A
   list without capacity owns nothing. *)
Definition arrayListBuffer `{!islaG Sigma} `{!threadG}
    (elementBytes log2Align : Z) (state : ArrayListState) : iProp Sigma :=
  (arrayListPointer state ↦ₘ∗ arrayListItems state ∗
   (arrayListPointer state + arrayListLength state * elementBytes) ↦ₘ?
     ((arrayListCapacity state - arrayListLength state) * elementBytes) ∗
   altFlBlock (arrayListPointer state)
     (arrayListCapacity state * elementBytes) log2Align)%I.
Global Instance : LithiumUnfold (@arrayListBuffer) := I.
Global Typeclasses Opaque arrayListBuffer.

Inductive ArrayListOutcomeKind : Type :=
| arrayListSuccess
| arrayListOutOfMemory.

Definition arrayListOutcomeCode (kind : ArrayListOutcomeKind) : Z :=
  match kind with
  | arrayListSuccess => 0
  | arrayListOutOfMemory => arrayListOutOfMemoryCode
  end.

(* Registers. The callee-saved registers return their entry values; the
   other general registers are owned with any 64-bit value. *)
Definition arrayListCalleeSaved : list string :=
  ["x8"; "x9"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"].
Definition arrayListEntryScratch : list string :=
  ["x5"; "x6"; "x7"; "x13"; "x14"; "x15"; "x16"; "x17"; "x28"; "x29";
   "x30"; "x31"].
Definition arrayListExitScratch : list string :=
  ["x5"; "x6"; "x7"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition arrayListSavedRegisters `{!islaG Sigma} `{!threadG}
    (saved : list (bv 64)) : iProp Sigma :=
  reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
    arrayListCalleeSaved ((fun value : bv 64 => RVal_Bits value) <$> saved)).
Global Instance : LithiumUnfold (@arrayListSavedRegisters) := I.
Global Typeclasses Opaque arrayListSavedRegisters.

Definition arrayListAnyRegisters `{!islaG Sigma} `{!threadG}
    (registers : list string) : iProp Sigma :=
  reg_col ((fun register => (KindReg register, BitsShape 64)) <$> registers).
Global Instance : LithiumUnfold (@arrayListAnyRegisters) := I.
Global Typeclasses Opaque arrayListAnyRegisters.

Definition arrayListStackLayout (stackPointer stackBytes : Z) : Prop :=
  (16 | stackPointer) /\
  mapRamBase defaultMap <= stackPointer - stackBytes /\
  stackPointer <= machineRamEnd defaultMap.

(* The error-union result {ptr, len, err:u16} of 24 bytes. Success writes
   ptr, len and err = 0; an error writes only err. Bytes 18..23 (padding)
   keep their entry values. *)
Definition arrayListResultImage (before : list byte) (pointer length : Z) :
    list byte :=
  word64Bytes pointer ++ word64Bytes length ++ firstn 2 (word64Bytes 0) ++
  skipn 18 before.
Definition arrayListErrorImage (before : list byte) (code : Z) : list byte :=
  firstn 16 before ++ firstn 2 (word64Bytes code) ++ skipn 18 before.

(* ---- toOwnedSlice(self: *List, gpa: Allocator) Allocator.Error!Slice ----
   a0 = result, a1 = list, a2 = allocator. *)

Record ToOwnedSliceArgs : Type := {
  toOwnedResultPointer : Z;
  toOwnedListPointer : Z;
  toOwnedAllocatorPointer : Z;
  toOwnedAllocatorContext : Z;
  toOwnedList : ArrayListState;
  toOwnedResultBefore : list byte;
  toOwnedStackPointer : Z;
  toOwnedReturnAddress : Z;
  toOwnedSaved : list (bv 64)
}.

(* The returned slice is a list whose capacity is its length: an allocator
   block of exactly length * elementBytes bytes, freed later with that
   length. *)
Record ToOwnedSliceOutcome : Type := {
  toOwnedKind : ArrayListOutcomeKind;
  toOwnedListAfter : ArrayListState;
  toOwnedSlice : ArrayListState;
  toOwnedResultAfter : list byte
}.

Definition toOwnedSliceDomain (elementBytes : Z) (args : ToOwnedSliceArgs) :
    Prop :=
  arrayListWellFormed elementBytes (toOwnedList args) /\
  arrayListRamRange (toOwnedResultPointer args) arrayListResultSize /\
  (8 | toOwnedResultPointer args) /\
  arrayListRamRange (toOwnedListPointer args) arrayListHeaderSize /\
  (8 | toOwnedListPointer args) /\
  arrayListRamRange (toOwnedAllocatorPointer args) arrayListAllocatorSize /\
  (8 | toOwnedAllocatorPointer args) /\
  Z.of_nat (length (toOwnedResultBefore args)) = arrayListResultSize /\
  0 <= toOwnedAllocatorContext args < 2 ^ 64 /\
  arrayListStackLayout (toOwnedStackPointer args)
    arrayListToOwnedSliceStackBytes /\
  0 <= toOwnedReturnAddress args < 2 ^ 64 /\
  (4 | toOwnedReturnAddress args) /\
  length (toOwnedSaved args) = 12%nat.

(* The machine code with alt_fl_alloc, whose remap always fails:
   - length 0: free the buffer (when it has capacity), return the old
     pointer with length 0, reset the list to the empty list;
   - otherwise alloc length * elementBytes bytes: on null return
     error.OutOfMemory (code 2) and keep the list; else copy the items, free
     the old buffer, set length and capacity to 0 (the pointer stays), and
     return the new block. *)
Definition toOwnedSliceAllows (elementBytes emptyPointer : Z)
    (args : ToOwnedSliceArgs) (outcome : ToOwnedSliceOutcome) : Prop :=
  let state := toOwnedList args in
  let before := toOwnedResultBefore args in
  arrayListWellFormed elementBytes (toOwnedListAfter outcome) /\
  arrayListWellFormed elementBytes (toOwnedSlice outcome) /\
  arrayListCapacity (toOwnedSlice outcome) =
    arrayListLength (toOwnedSlice outcome) /\
  (if arrayListLength state =? 0 then
     toOwnedKind outcome = arrayListSuccess /\
     toOwnedListAfter outcome = arrayListEmpty emptyPointer /\
     toOwnedSlice outcome = arrayListEmpty (arrayListPointer state) /\
     toOwnedResultAfter outcome =
       arrayListResultImage before (arrayListPointer state) 0
   else
     match toOwnedKind outcome with
     | arrayListSuccess =>
         toOwnedListAfter outcome = arrayListEmpty (arrayListPointer state) /\
         arrayListLength (toOwnedSlice outcome) = arrayListLength state /\
         arrayListItems (toOwnedSlice outcome) = arrayListItems state /\
         toOwnedResultAfter outcome =
           arrayListResultImage before
             (arrayListPointer (toOwnedSlice outcome)) (arrayListLength state)
     | arrayListOutOfMemory =>
         toOwnedListAfter outcome = state /\
         toOwnedSlice outcome = arrayListEmpty emptyPointer /\
         toOwnedResultAfter outcome =
           arrayListErrorImage before arrayListOutOfMemoryCode
     end).

Definition toOwnedSliceEntry `{!islaG Sigma} `{!threadG}
    (elementBytes log2Align : Z) (args : ToOwnedSliceArgs) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (toOwnedReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (toOwnedStackPointer args)) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (toOwnedResultPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (toOwnedListPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (toOwnedAllocatorPointer args)) ∗
   arrayListSavedRegisters (toOwnedSaved args) ∗
   arrayListAnyRegisters arrayListEntryScratch ∗
   toOwnedListPointer args ↦ₘ∗ arrayListHeaderBytes (toOwnedList args) ∗
   arrayListBuffer elementBytes log2Align (toOwnedList args) ∗
   toOwnedResultPointer args ↦ₘ∗ toOwnedResultBefore args ∗
   altFlAllocatorObject (toOwnedAllocatorPointer args)
     (toOwnedAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (toOwnedStackPointer args - arrayListToOwnedSliceStackBytes) ↦ₘ?
     arrayListToOwnedSliceStackBytes ∗
   ⌜toOwnedSliceDomain elementBytes args⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@toOwnedSliceEntry) := I.
Global Typeclasses Opaque toOwnedSliceEntry.

(* The list keeps the buffer of its after-state: all of it on
   OutOfMemory, nothing after success. The returned slice owns its block. *)
Definition toOwnedSliceExit `{!islaG Sigma} `{!threadG}
    (elementBytes log2Align : Z) (args : ToOwnedSliceArgs)
    (outcome : ToOwnedSliceOutcome) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (toOwnedReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (toOwnedStackPointer args)) ∗
   arrayListSavedRegisters (toOwnedSaved args) ∗
   arrayListAnyRegisters ("x10" :: arrayListExitScratch) ∗
   toOwnedListPointer args ↦ₘ∗ arrayListHeaderBytes (toOwnedListAfter outcome) ∗
   arrayListBuffer elementBytes log2Align (toOwnedListAfter outcome) ∗
   arrayListBuffer elementBytes log2Align (toOwnedSlice outcome) ∗
   toOwnedResultPointer args ↦ₘ∗ toOwnedResultAfter outcome ∗
   altFlAllocatorObject (toOwnedAllocatorPointer args)
     (toOwnedAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (toOwnedStackPointer args - arrayListToOwnedSliceStackBytes) ↦ₘ?
     arrayListToOwnedSliceStackBytes ∗ True)%I.
Global Instance : LithiumUnfold (@toOwnedSliceExit) := I.
Global Typeclasses Opaque toOwnedSliceExit.

Definition toOwnedSliceResources `{!islaG Sigma} `{!threadG}
    (code : iProp Sigma) (elementBytes log2Align returnAddress : Z) :
    IslarisContractResources ToOwnedSliceArgs ToOwnedSliceOutcome :=
  {| islarisCode := code;
     islarisEntry := fun args =>
       (⌜toOwnedReturnAddress args = returnAddress⌝ ∗
        toOwnedSliceEntry elementBytes log2Align args)%I;
     islarisExit := toOwnedSliceExit elementBytes log2Align |}.

Definition toOwnedSliceModel
    (code : forall (Sigma : gFunctors), islaG Sigma -> threadG -> iProp Sigma)
    (step : Z -> Z -> Prop)
    (elementBytes log2Align emptyPointer returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  {| islarisContractAllows := fun args outcome =>
       toOwnedReturnAddress args = returnAddress /\
       toOwnedSliceDomain elementBytes args /\
       toOwnedSliceAllows elementBytes emptyPointer args outcome;
     islarisContractStep := step;
     islarisContractResources := fun Sigma HG HT =>
       @toOwnedSliceResources Sigma HG HT (code Sigma HG HT)
         elementBytes log2Align returnAddress |}.

(* The ranges and links of the folded domain as plain facts. *)
Lemma toOwnedSliceDomainRanges (elementBytes : Z) (args : ToOwnedSliceArgs) :
  toOwnedSliceDomain elementBytes args ->
  0 <= arrayListLength (toOwnedList args) <=
    arrayListCapacity (toOwnedList args) /\
  Z.of_nat (length (arrayListItems (toOwnedList args))) =
    arrayListLength (toOwnedList args) * elementBytes /\
  0 < arrayListPointer (toOwnedList args) < 2 ^ 64 /\
  (0 < arrayListCapacity (toOwnedList args) ->
    mapRamBase defaultMap <= arrayListPointer (toOwnedList args) /\
    arrayListPointer (toOwnedList args) +
      arrayListCapacity (toOwnedList args) * elementBytes <=
      machineRamEnd defaultMap) /\
  mapRamBase defaultMap <= toOwnedResultPointer args /\
  toOwnedResultPointer args + arrayListResultSize <= machineRamEnd defaultMap /\
  (8 | toOwnedResultPointer args) /\
  mapRamBase defaultMap <= toOwnedListPointer args /\
  toOwnedListPointer args + arrayListHeaderSize <= machineRamEnd defaultMap /\
  (8 | toOwnedListPointer args) /\
  mapRamBase defaultMap <= toOwnedAllocatorPointer args /\
  toOwnedAllocatorPointer args + arrayListAllocatorSize <=
    machineRamEnd defaultMap /\
  (8 | toOwnedAllocatorPointer args) /\
  Z.of_nat (length (toOwnedResultBefore args)) = arrayListResultSize /\
  0 <= toOwnedAllocatorContext args < 2 ^ 64 /\
  (16 | toOwnedStackPointer args) /\
  mapRamBase defaultMap <=
    toOwnedStackPointer args - arrayListToOwnedSliceStackBytes /\
  toOwnedStackPointer args <= machineRamEnd defaultMap /\
  0 <= toOwnedReturnAddress args < 2 ^ 64 /\
  (4 | toOwnedReturnAddress args) /\
  length (toOwnedSaved args) = 12%nat.
Proof.
  unfold toOwnedSliceDomain, arrayListWellFormed, arrayListRamRange,
    arrayListStackLayout.
  tauto.
Qed.

#[export] Instance toOwnedSliceDomainRangesInstance
    (elementBytes : Z) (args : ToOwnedSliceArgs) :
  ZesuDomainRanges (toOwnedSliceDomain elementBytes args) _ :=
  toOwnedSliceDomainRanges elementBytes args.
