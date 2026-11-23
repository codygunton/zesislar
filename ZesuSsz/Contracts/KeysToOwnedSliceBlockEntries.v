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

(* Block-entry form of the keysToOwnedSlice contract (KeysToOwnedSliceContract.v)
   for the block generator: every register, array and word the code reads is a
   separate conjunct in a shape tools/block/functions/entry_interface_inputs.py
   reads. Not a statement of the trust base: the region theorem proves that
   toOwnedSliceEntry at keys' constants implies this entry, and this exit
   implies toOwnedSliceExit.
   Registers are bv 64 binders with their machine bounds on bv_unsigned; each
   binder's link to the contract quantity is a separate pure conjunct (F44). *)

Notation keysBlockFrameBytes := ((96) : Z) (only parsing).
(* The prologue saves ra, s0-s8 in the top 80 bytes of the frame; the lowest
   16 bytes are scratch. Separate regions, so the saved words fill their region
   and the entries state one cell per saved-register slot (profile frame_slots). *)
Notation keysBlockSavedBytes := ((80) : Z) (only parsing).
Notation keysBlockScratchBytes := ((16) : Z) (only parsing).
Notation keysBlockCalleeBytes := ((16) : Z) (only parsing).
Notation keysBlockRamLow := ((0xa0000000) : Z) (only parsing).
Notation keysBlockRamHigh := ((0xc0000000) : Z) (only parsing).
Notation keysBlockHeaderBytes := ((24) : Z) (only parsing).
Notation keysBlockResultBytes := ((24) : Z) (only parsing).
Notation keysBlockAllocatorBytes := ((16) : Z) (only parsing).

Record KeysToOwnedSliceBlockArgs : Type := {
  keysBase : ToOwnedSliceArgs;
  keysReturnAddress : bv 64; keysStackPointer : bv 64;
  keysResultPointer : bv 64; keysListPointer : bv 64;
  keysAllocatorPointer : bv 64;
  keysSavedX8 : bv 64; keysSavedX9 : bv 64;
  keysSavedX18 : bv 64; keysSavedX19 : bv 64; keysSavedX20 : bv 64;
  keysSavedX21 : bv 64; keysSavedX22 : bv 64; keysSavedX23 : bv 64;
  keysSavedX24 : bv 64; keysSavedX25 : bv 64; keysSavedX26 : bv 64;
  keysSavedX27 : bv 64
}.

(* The little-endian word of a byte list at an offset (the word-link reader). *)
Definition keysBlockWord (bytes : list byte) (offset : Z) : Z :=
  little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset) bytes)).

Definition keysBlockList (args : KeysToOwnedSliceBlockArgs) : ArrayListState :=
  toOwnedList (keysBase args).

Definition keysBlockArgsWellFormed (args : KeysToOwnedSliceBlockArgs) : Prop :=
  0 <= arrayListLength (keysBlockList args) <= 2 ^ 24 /\
  0 <= arrayListCapacity (keysBlockList args) <= 2 ^ 24 /\
  arrayListLength (keysBlockList args) <= arrayListCapacity (keysBlockList args) /\
  1 <= arrayListPointer (keysBlockList args) < 2 ^ 64 /\
  Z.of_nat (length (arrayListItems (keysBlockList args))) =
    arrayListLength (keysBlockList args) * keysElementBytes /\
  toOwnedSliceDomain keysElementBytes (keysBase args) /\
  toOwnedSaved (keysBase args) =
    [keysSavedX8 args; keysSavedX9 args; keysSavedX18 args; keysSavedX19 args;
     keysSavedX20 args; keysSavedX21 args; keysSavedX22 args; keysSavedX23 args;
     keysSavedX24 args; keysSavedX25 args; keysSavedX26 args; keysSavedX27 args] /\
  length (toOwnedScratchBefore (keysBase args)) = 8%nat /\
  length (toOwnedResultBefore (keysBase args)) = 24%nat /\
  length (arrayListHeaderBytes (keysBlockList args)) = 24%nat /\
  length (altFlAllocatorBytes (toOwnedAllocatorContext (keysBase args))) = 16%nat /\
  length altFlVtableBytes = 32%nat /\
  toOwnedReturnAddress (keysBase args) = bv_unsigned (keysReturnAddress args) /\
  toOwnedStackPointer (keysBase args) = bv_unsigned (keysStackPointer args) /\
  toOwnedResultPointer (keysBase args) = bv_unsigned (keysResultPointer args) /\
  toOwnedListPointer (keysBase args) = bv_unsigned (keysListPointer args) /\
  toOwnedAllocatorPointer (keysBase args) = bv_unsigned (keysAllocatorPointer args) /\
  keysBlockRamLow <= bv_unsigned (keysResultPointer args) /\
  bv_unsigned (keysResultPointer args) + keysBlockResultBytes <= keysBlockRamHigh /\
  bv_unsigned (keysResultPointer args) mod 8 = 0 /\
  keysBlockRamLow <= bv_unsigned (keysListPointer args) /\
  bv_unsigned (keysListPointer args) + keysBlockHeaderBytes <= keysBlockRamHigh /\
  bv_unsigned (keysListPointer args) mod 8 = 0 /\
  keysBlockRamLow <= bv_unsigned (keysAllocatorPointer args) /\
  bv_unsigned (keysAllocatorPointer args) + keysBlockAllocatorBytes <= keysBlockRamHigh /\
  bv_unsigned (keysAllocatorPointer args) mod 8 = 0 /\
  keysBlockRamLow + keysBlockFrameBytes + keysBlockCalleeBytes <=
    bv_unsigned (keysStackPointer args) <= keysBlockRamHigh /\
  bv_unsigned (keysStackPointer args) mod 16 = 0 /\
  bv_unsigned (keysReturnAddress args) mod 4 = 0 /\
  keysBlockWord (arrayListHeaderBytes (keysBlockList args)) 0 =
    arrayListPointer (keysBlockList args) /\
  keysBlockWord (arrayListHeaderBytes (keysBlockList args)) 8 =
    arrayListLength (keysBlockList args) /\
  keysBlockWord (arrayListHeaderBytes (keysBlockList args)) 16 =
    arrayListCapacity (keysBlockList args) /\
  keysBlockWord (altFlAllocatorBytes (toOwnedAllocatorContext (keysBase args))) 0 =
    toOwnedAllocatorContext (keysBase args) /\
  keysBlockWord (altFlAllocatorBytes (toOwnedAllocatorContext (keysBase args))) 8 =
    sym_alt_fl_alloc_vtable /\
  keysBlockWord altFlVtableBytes 0 = sym_alt_fl_alloc_alloc /\
  keysBlockWord altFlVtableBytes 16 = sym_alt_fl_alloc_remap /\
  keysBlockWord altFlVtableBytes 24 = sym_alt_fl_alloc_free.

Definition keysBlockEntryResources `{!islaG Sigma} `{!threadG}
    (args : KeysToOwnedSliceBlockArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (keysReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (keysStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (keysSavedX8 args) ∗
   "x9" ↦ᵣ RVal_Bits (keysSavedX9 args) ∗
   "x10" ↦ᵣ RVal_Bits (keysResultPointer args) ∗
   "x11" ↦ᵣ RVal_Bits (keysListPointer args) ∗
   "x12" ↦ᵣ RVal_Bits (keysAllocatorPointer args) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (keysSavedX18 args) ∗
   "x19" ↦ᵣ RVal_Bits (keysSavedX19 args) ∗
   "x20" ↦ᵣ RVal_Bits (keysSavedX20 args) ∗
   "x21" ↦ᵣ RVal_Bits (keysSavedX21 args) ∗
   "x22" ↦ᵣ RVal_Bits (keysSavedX22 args) ∗
   "x23" ↦ᵣ RVal_Bits (keysSavedX23 args) ∗
   "x24" ↦ᵣ RVal_Bits (keysSavedX24 args) ∗
   "x25" ↦ᵣ RVal_Bits (keysSavedX25 args) ∗
   "x26" ↦ᵣ RVal_Bits (keysSavedX26 args) ∗
   "x27" ↦ᵣ RVal_Bits (keysSavedX27 args) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   bv_unsigned (keysListPointer args) ↦ₘ∗ arrayListHeaderBytes (keysBlockList args) ∗
   arrayListPointer (keysBlockList args) ↦ₘ∗ arrayListItems (keysBlockList args) ∗
   (arrayListPointer (keysBlockList args) +
      arrayListLength (keysBlockList args) * keysElementBytes) ↦ₘ?
     ((arrayListCapacity (keysBlockList args) - arrayListLength (keysBlockList args)) *
        keysElementBytes) ∗
   altFlBlock (arrayListPointer (keysBlockList args))
     (arrayListCapacity (keysBlockList args) * keysElementBytes) keysLog2Alignment ∗
   bv_unsigned (keysResultPointer args) ↦ₘ∗ toOwnedResultBefore (keysBase args) ∗
   bv_unsigned (keysAllocatorPointer args) ↦ₘ∗
     altFlAllocatorBytes (toOwnedAllocatorContext (keysBase args)) ∗
   sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes ∗
   altFlHeap ∗
   ziskExtraParamsAddress ↦ₘ∗ toOwnedScratchBefore (keysBase args) ∗
   (bv_unsigned (keysStackPointer args) - keysBlockFrameBytes) ↦ₘ? keysBlockScratchBytes ∗
   (bv_unsigned (keysStackPointer args) - keysBlockSavedBytes) ↦ₘ? keysBlockSavedBytes ∗
   (bv_unsigned (keysStackPointer args) - keysBlockFrameBytes - keysBlockCalleeBytes) ↦ₘ?
     keysBlockCalleeBytes ∗
   ⌜keysBlockArgsWellFormed args⌝ ∗ True)%I.

(* The exit: toOwnedSliceExit at the outcome with the registers and addresses
   of the entry binders; under the entry's links it is the contract's exit. *)
Definition keysBlockExitResources `{!islaG Sigma} `{!threadG}
    (args : KeysToOwnedSliceBlockArgs) (outcome : ToOwnedSliceOutcome) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (keysReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (keysStackPointer args) ∗
   arrayListSavedRegisters (toOwnedSaved (keysBase args)) ∗
   arrayListAnyRegisters ("x10" :: arrayListExitScratch) ∗
   bv_unsigned (keysListPointer args) ↦ₘ∗ arrayListHeaderBytes (toOwnedListAfter outcome) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (toOwnedListAfter outcome) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (toOwnedSlice outcome) ∗
   bv_unsigned (keysResultPointer args) ↦ₘ∗ toOwnedResultAfter outcome ∗
   ziskExtraParamsAddress ↦ₘ∗
     toOwnedSliceScratchAfter keysElementBytes (keysBase args) outcome ∗
   altFlAllocatorObject (bv_unsigned (keysAllocatorPointer args))
     (toOwnedAllocatorContext (keysBase args)) ∗
   altFlVtable ∗
   altFlHeap ∗
   (bv_unsigned (keysStackPointer args) - arrayListToOwnedSliceStackBytes) ↦ₘ?
     arrayListToOwnedSliceStackBytes ∗ True)%I.

Definition keysBlockDomainAt (returnAddress : Z) (args : KeysToOwnedSliceBlockArgs) : Prop :=
  bv_unsigned (keysReturnAddress args) = returnAddress /\ keysBlockArgsWellFormed args.
