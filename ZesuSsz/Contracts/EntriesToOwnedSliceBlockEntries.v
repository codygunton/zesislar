From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ArrayListContract.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* Block-entry form of the entriesToOwnedSlice contract (EntriesToOwnedSliceContract.v)
   for the block generator: every register, array and word the code reads is a
   separate conjunct in a shape tools/block/functions/entry_interface_inputs.py
   reads. Not a statement of the trust base: the region theorem proves that
   toOwnedSliceEntry at entries' constants implies this entry; the exit is
   toOwnedSliceExit. The registers are the contract's bv 64 fields, bounded on
   bv_unsigned (F44). *)

Notation entriesBlockFrameBytes := ((96) : Z) (only parsing).
(* The prologue saves ra, s0-s8 in the top 80 bytes of the frame; the lowest
   16 bytes are scratch. Separate regions, so the saved words fill their region
   and the entries state one cell per saved-register slot (profile frame_slots). *)
Notation entriesBlockSavedBytes := ((80) : Z) (only parsing).
Notation entriesBlockScratchBytes := ((16) : Z) (only parsing).
Notation entriesBlockCalleeBytes := ((16) : Z) (only parsing).
Notation entriesBlockRamLow := ((0xa0000000) : Z) (only parsing).
Notation entriesBlockRamHigh := ((0xc0000000) : Z) (only parsing).
Notation entriesBlockHeaderBytes := ((24) : Z) (only parsing).
Notation entriesBlockResultBytes := ((24) : Z) (only parsing).
Notation entriesBlockAllocatorBytes := ((16) : Z) (only parsing).

Record EntriesToOwnedSliceBlockArgs : Type := {
  entriesBase : ToOwnedSliceArgs
}.

(* The little-endian word of a byte list at an offset (the word-link reader). *)
Definition entriesBlockWord (bytes : list byte) (offset : Z) : Z :=
  little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset) bytes)).

Definition entriesBlockList (args : EntriesToOwnedSliceBlockArgs) : ArrayListState :=
  toOwnedList (entriesBase args).

Definition entriesBlockArgsWellFormed (args : EntriesToOwnedSliceBlockArgs) : Prop :=
  0 <= arrayListLength (entriesBlockList args) <= 2 ^ 24 /\
  0 <= arrayListCapacity (entriesBlockList args) <= 2 ^ 24 /\
  arrayListLength (entriesBlockList args) <= arrayListCapacity (entriesBlockList args) /\
  1 <= arrayListPointer (entriesBlockList args) < 2 ^ 64 /\
  Z.of_nat (length (arrayListItems (entriesBlockList args))) =
    arrayListLength (entriesBlockList args) * entriesElementBytes /\
  toOwnedSliceDomain entriesElementBytes (entriesBase args) /\
  length (toOwnedScratchBefore (entriesBase args)) = 8%nat /\
  length (toOwnedResultBefore (entriesBase args)) = 24%nat /\
  length (arrayListHeaderBytes (entriesBlockList args)) = 24%nat /\
  length (altFlAllocatorBytes (toOwnedAllocatorContext (entriesBase args))) = 16%nat /\
  length altFlVtableBytes = 32%nat /\
  entriesBlockRamLow <= bv_unsigned (toOwnedResultPointer (entriesBase args)) /\
  bv_unsigned (toOwnedResultPointer (entriesBase args)) + entriesBlockResultBytes <= entriesBlockRamHigh /\
  bv_unsigned (toOwnedResultPointer (entriesBase args)) mod 8 = 0 /\
  entriesBlockRamLow <= bv_unsigned (toOwnedListPointer (entriesBase args)) /\
  bv_unsigned (toOwnedListPointer (entriesBase args)) + entriesBlockHeaderBytes <= entriesBlockRamHigh /\
  bv_unsigned (toOwnedListPointer (entriesBase args)) mod 8 = 0 /\
  entriesBlockRamLow <= bv_unsigned (toOwnedAllocatorPointer (entriesBase args)) /\
  bv_unsigned (toOwnedAllocatorPointer (entriesBase args)) + entriesBlockAllocatorBytes <=
    entriesBlockRamHigh /\
  bv_unsigned (toOwnedAllocatorPointer (entriesBase args)) mod 8 = 0 /\
  entriesBlockRamLow + entriesBlockFrameBytes + entriesBlockCalleeBytes <=
    bv_unsigned (toOwnedStackPointer (entriesBase args)) <= entriesBlockRamHigh /\
  bv_unsigned (toOwnedStackPointer (entriesBase args)) mod 16 = 0 /\
  bv_unsigned (toOwnedReturnAddress (entriesBase args)) mod 4 = 0 /\
  entriesBlockWord (arrayListHeaderBytes (entriesBlockList args)) 0 =
    arrayListPointer (entriesBlockList args) /\
  entriesBlockWord (arrayListHeaderBytes (entriesBlockList args)) 8 =
    arrayListLength (entriesBlockList args) /\
  entriesBlockWord (arrayListHeaderBytes (entriesBlockList args)) 16 =
    arrayListCapacity (entriesBlockList args) /\
  entriesBlockWord (altFlAllocatorBytes (toOwnedAllocatorContext (entriesBase args))) 0 =
    toOwnedAllocatorContext (entriesBase args) /\
  entriesBlockWord (altFlAllocatorBytes (toOwnedAllocatorContext (entriesBase args))) 8 =
    sym_alt_fl_alloc_vtable /\
  entriesBlockWord altFlVtableBytes 0 = sym_alt_fl_alloc_alloc /\
  entriesBlockWord altFlVtableBytes 16 = sym_alt_fl_alloc_remap /\
  entriesBlockWord altFlVtableBytes 24 = sym_alt_fl_alloc_free.

Definition entriesBlockEntryResources `{!islaG Sigma} `{!threadG}
    (args : EntriesToOwnedSliceBlockArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (arrayListSysRegs (toOwnedInputEnd (entriesBase args))) ∗
   "x1" ↦ᵣ RVal_Bits (toOwnedReturnAddress (entriesBase args)) ∗
   "x2" ↦ᵣ RVal_Bits (toOwnedStackPointer (entriesBase args)) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (savedX8 (toOwnedSaved (entriesBase args))) ∗
   "x9" ↦ᵣ RVal_Bits (savedX9 (toOwnedSaved (entriesBase args))) ∗
   "x10" ↦ᵣ RVal_Bits (toOwnedResultPointer (entriesBase args)) ∗
   "x11" ↦ᵣ RVal_Bits (toOwnedListPointer (entriesBase args)) ∗
   "x12" ↦ᵣ RVal_Bits (toOwnedAllocatorPointer (entriesBase args)) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (savedX18 (toOwnedSaved (entriesBase args))) ∗
   "x19" ↦ᵣ RVal_Bits (savedX19 (toOwnedSaved (entriesBase args))) ∗
   "x20" ↦ᵣ RVal_Bits (savedX20 (toOwnedSaved (entriesBase args))) ∗
   "x21" ↦ᵣ RVal_Bits (savedX21 (toOwnedSaved (entriesBase args))) ∗
   "x22" ↦ᵣ RVal_Bits (savedX22 (toOwnedSaved (entriesBase args))) ∗
   "x23" ↦ᵣ RVal_Bits (savedX23 (toOwnedSaved (entriesBase args))) ∗
   "x24" ↦ᵣ RVal_Bits (savedX24 (toOwnedSaved (entriesBase args))) ∗
   "x25" ↦ᵣ RVal_Bits (savedX25 (toOwnedSaved (entriesBase args))) ∗
   "x26" ↦ᵣ RVal_Bits (savedX26 (toOwnedSaved (entriesBase args))) ∗
   "x27" ↦ᵣ RVal_Bits (savedX27 (toOwnedSaved (entriesBase args))) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   bv_unsigned (toOwnedListPointer (entriesBase args)) ↦ₘ∗
     arrayListHeaderBytes (entriesBlockList args) ∗
   arrayListPointer (entriesBlockList args) ↦ₘ∗ arrayListItems (entriesBlockList args) ∗
   (arrayListPointer (entriesBlockList args) +
      arrayListLength (entriesBlockList args) * entriesElementBytes) ↦ₘ?
     ((arrayListCapacity (entriesBlockList args) - arrayListLength (entriesBlockList args)) *
        entriesElementBytes) ∗
   altFlBlock (arrayListPointer (entriesBlockList args))
     (arrayListCapacity (entriesBlockList args) * entriesElementBytes) entriesLog2Alignment ∗
   bv_unsigned (toOwnedResultPointer (entriesBase args)) ↦ₘ∗
     toOwnedResultBefore (entriesBase args) ∗
   bv_unsigned (toOwnedAllocatorPointer (entriesBase args)) ↦ₘ∗
     altFlAllocatorBytes (toOwnedAllocatorContext (entriesBase args)) ∗
   sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes ∗
   altFlHeap ∗
   ziskExtraParamsAddress ↦ₘ∗ toOwnedScratchBefore (entriesBase args) ∗
   (bv_unsigned (toOwnedStackPointer (entriesBase args)) - entriesBlockFrameBytes) ↦ₘ?
     entriesBlockScratchBytes ∗
   (bv_unsigned (toOwnedStackPointer (entriesBase args)) - entriesBlockSavedBytes) ↦ₘ?
     entriesBlockSavedBytes ∗
   (bv_unsigned (toOwnedStackPointer (entriesBase args)) - entriesBlockFrameBytes -
      entriesBlockCalleeBytes) ↦ₘ?
     entriesBlockCalleeBytes ∗
   ⌜entriesBlockArgsWellFormed args⌝ ∗ True)%I.

(* The exit: the contract's exit at the outcome. *)
Definition entriesBlockExitResources `{!islaG Sigma} `{!threadG}
    (args : EntriesToOwnedSliceBlockArgs) (outcome : ToOwnedSliceOutcome) : iProp Sigma :=
  toOwnedSliceExit entriesElementBytes entriesLog2Alignment (entriesBase args) outcome.

Definition entriesBlockDomainAt (returnAddress : Z) (args : EntriesToOwnedSliceBlockArgs) : Prop :=
  bv_unsigned (toOwnedReturnAddress (entriesBase args)) = returnAddress /\
  entriesBlockArgsWellFormed args.
