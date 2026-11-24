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
Require Import ZesuSsz.Contracts.KeysEnsureCapacityContract.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* Block-entry form of the keysEnsureCapacity contract
   (KeysEnsureCapacityContract.v) for the block generator: every register,
   array and word the code reads is a separate conjunct in a shape
   tools/block/functions/entry_interface_inputs.py reads. Not a statement of
   the trust base: the region theorem proves that keysEnsureCapacityEntry
   implies this entry; the exit is keysEnsureCapacityExit. The registers are
   the contract's bv 64 fields, bounded on bv_unsigned (F44). *)

Notation ensureBlockFrameBytes := ((112) : Z) (only parsing).
(* The prologue saves ra, s0-s9 in the top 88 bytes of the frame; the lowest
   24 bytes are scratch. Separate regions, so the saved words fill their
   region and the entries state one cell per saved-register slot (profile
   frame_slots). *)
Notation ensureBlockSavedBytes := ((88) : Z) (only parsing).
Notation ensureBlockScratchBytes := ((24) : Z) (only parsing).
Notation ensureBlockCalleeBytes := ((16) : Z) (only parsing).
Notation ensureBlockRamLow := ((0xa0000000) : Z) (only parsing).
Notation ensureBlockRamHigh := ((0xc0000000) : Z) (only parsing).
Notation ensureBlockHeaderBytes := ((24) : Z) (only parsing).
Notation ensureBlockAllocatorBytes := ((16) : Z) (only parsing).
(* keysEnsureCapacityMaxRequest (2 ^ 32) as a numeral, the form the inputs tool reads. *)
Notation ensureBlockMaxRequest := ((4294967296) : Z) (only parsing).

Record KeysEnsureCapacityBlockArgs : Type := {
  ensureBase : EnsureCapacityArgs
}.

(* The little-endian word of a byte list at an offset (the word-link reader). *)
Definition ensureBlockWord (bytes : list byte) (offset : Z) : Z :=
  little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset) bytes)).

Definition ensureBlockList (args : KeysEnsureCapacityBlockArgs) : ArrayListState :=
  ensureList (ensureBase args).

Definition ensureBlockArgsWellFormed (args : KeysEnsureCapacityBlockArgs) : Prop :=
  0 <= arrayListLength (ensureBlockList args) <= 2 ^ 24 /\
  0 <= arrayListCapacity (ensureBlockList args) <= 2 ^ 24 /\
  arrayListLength (ensureBlockList args) <= arrayListCapacity (ensureBlockList args) /\
  1 <= arrayListPointer (ensureBlockList args) < 2 ^ 64 /\
  Z.of_nat (length (arrayListItems (ensureBlockList args))) =
    arrayListLength (ensureBlockList args) * keysElementBytes /\
  0 <= bv_unsigned (ensureRequested (ensureBase args)) < ensureBlockMaxRequest /\
  keysEnsureCapacityDomain (ensureBase args) /\
  length (ensureScratchBefore (ensureBase args)) = 8%nat /\
  length (arrayListHeaderBytes (ensureBlockList args)) = 24%nat /\
  length (altFlAllocatorBytes (ensureAllocatorContext (ensureBase args))) = 16%nat /\
  length altFlVtableBytes = 32%nat /\
  ensureBlockRamLow <= bv_unsigned (ensureListPointer (ensureBase args)) /\
  bv_unsigned (ensureListPointer (ensureBase args)) + ensureBlockHeaderBytes <=
    ensureBlockRamHigh /\
  bv_unsigned (ensureListPointer (ensureBase args)) mod 8 = 0 /\
  ensureBlockRamLow <= bv_unsigned (ensureAllocatorPointer (ensureBase args)) /\
  bv_unsigned (ensureAllocatorPointer (ensureBase args)) + ensureBlockAllocatorBytes <=
    ensureBlockRamHigh /\
  bv_unsigned (ensureAllocatorPointer (ensureBase args)) mod 8 = 0 /\
  ensureBlockRamLow + ensureBlockFrameBytes + ensureBlockCalleeBytes <=
    bv_unsigned (ensureStackPointer (ensureBase args)) <= ensureBlockRamHigh /\
  bv_unsigned (ensureStackPointer (ensureBase args)) mod 16 = 0 /\
  bv_unsigned (ensureReturnAddress (ensureBase args)) mod 4 = 0 /\
  ensureBlockWord (arrayListHeaderBytes (ensureBlockList args)) 0 =
    arrayListPointer (ensureBlockList args) /\
  ensureBlockWord (arrayListHeaderBytes (ensureBlockList args)) 8 =
    arrayListLength (ensureBlockList args) /\
  ensureBlockWord (arrayListHeaderBytes (ensureBlockList args)) 16 =
    arrayListCapacity (ensureBlockList args) /\
  ensureBlockWord (altFlAllocatorBytes (ensureAllocatorContext (ensureBase args))) 0 =
    ensureAllocatorContext (ensureBase args) /\
  ensureBlockWord (altFlAllocatorBytes (ensureAllocatorContext (ensureBase args))) 8 =
    sym_alt_fl_alloc_vtable /\
  ensureBlockWord altFlVtableBytes 0 = sym_alt_fl_alloc_alloc /\
  ensureBlockWord altFlVtableBytes 16 = sym_alt_fl_alloc_remap /\
  ensureBlockWord altFlVtableBytes 24 = sym_alt_fl_alloc_free.

Definition ensureBlockEntryResources `{!islaG Sigma} `{!threadG}
    (args : KeysEnsureCapacityBlockArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (arrayListSysRegs (ensureInputEnd (ensureBase args))) ∗
   "x1" ↦ᵣ RVal_Bits (ensureReturnAddress (ensureBase args)) ∗
   "x2" ↦ᵣ RVal_Bits (ensureStackPointer (ensureBase args)) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (savedX8 (ensureSaved (ensureBase args))) ∗
   "x9" ↦ᵣ RVal_Bits (savedX9 (ensureSaved (ensureBase args))) ∗
   "x10" ↦ᵣ RVal_Bits (ensureListPointer (ensureBase args)) ∗
   "x11" ↦ᵣ RVal_Bits (ensureAllocatorPointer (ensureBase args)) ∗
   "x12" ↦ᵣ RVal_Bits (ensureRequested (ensureBase args)) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (savedX18 (ensureSaved (ensureBase args))) ∗
   "x19" ↦ᵣ RVal_Bits (savedX19 (ensureSaved (ensureBase args))) ∗
   "x20" ↦ᵣ RVal_Bits (savedX20 (ensureSaved (ensureBase args))) ∗
   "x21" ↦ᵣ RVal_Bits (savedX21 (ensureSaved (ensureBase args))) ∗
   "x22" ↦ᵣ RVal_Bits (savedX22 (ensureSaved (ensureBase args))) ∗
   "x23" ↦ᵣ RVal_Bits (savedX23 (ensureSaved (ensureBase args))) ∗
   "x24" ↦ᵣ RVal_Bits (savedX24 (ensureSaved (ensureBase args))) ∗
   "x25" ↦ᵣ RVal_Bits (savedX25 (ensureSaved (ensureBase args))) ∗
   "x26" ↦ᵣ RVal_Bits (savedX26 (ensureSaved (ensureBase args))) ∗
   "x27" ↦ᵣ RVal_Bits (savedX27 (ensureSaved (ensureBase args))) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   bv_unsigned (ensureListPointer (ensureBase args)) ↦ₘ∗
     arrayListHeaderBytes (ensureBlockList args) ∗
   arrayListPointer (ensureBlockList args) ↦ₘ∗ arrayListItems (ensureBlockList args) ∗
   (arrayListPointer (ensureBlockList args) +
      arrayListLength (ensureBlockList args) * keysElementBytes) ↦ₘ?
     ((arrayListCapacity (ensureBlockList args) - arrayListLength (ensureBlockList args)) *
        keysElementBytes) ∗
   altFlBlock (arrayListPointer (ensureBlockList args))
     (arrayListCapacity (ensureBlockList args) * keysElementBytes) keysLog2Alignment ∗
   bv_unsigned (ensureAllocatorPointer (ensureBase args)) ↦ₘ∗
     altFlAllocatorBytes (ensureAllocatorContext (ensureBase args)) ∗
   sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes ∗
   altFlHeap ∗
   ziskExtraParamsAddress ↦ₘ∗ ensureScratchBefore (ensureBase args) ∗
   (bv_unsigned (ensureStackPointer (ensureBase args)) - ensureBlockFrameBytes) ↦ₘ?
     ensureBlockScratchBytes ∗
   (bv_unsigned (ensureStackPointer (ensureBase args)) - ensureBlockSavedBytes) ↦ₘ?
     ensureBlockSavedBytes ∗
   (bv_unsigned (ensureStackPointer (ensureBase args)) - ensureBlockFrameBytes -
      ensureBlockCalleeBytes) ↦ₘ?
     ensureBlockCalleeBytes ∗
   ⌜ensureBlockArgsWellFormed args⌝ ∗ True)%I.

(* The exit: the contract's exit at the outcome. *)
Definition ensureBlockExitResources `{!islaG Sigma} `{!threadG}
    (args : KeysEnsureCapacityBlockArgs) (outcome : EnsureCapacityOutcome) : iProp Sigma :=
  keysEnsureCapacityExit (ensureBase args) outcome.

Definition ensureBlockDomainAt (returnAddress : Z) (args : KeysEnsureCapacityBlockArgs) : Prop :=
  bv_unsigned (ensureReturnAddress (ensureBase args)) = returnAddress /\
  ensureBlockArgsWellFormed args.
