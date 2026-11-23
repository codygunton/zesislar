From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Stock.Closure.index_txAccessList.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Stock.Closure.index_ensureTotalCapacity.
Require Import ZesuSsz.Stock.Closure.index_sliceBytes32.
Require Import ZesuSsz.Stock.Closure.index_sliceAccessList.
Require Import ZesuSsz.Stock.Closure.index_allocatorAlloc.
Require Import ZesuSsz.Stock.Closure.index_allocatorRemap.
Require Import ZesuSsz.Stock.Closure.index_allocatorFree.
Require Import ZesuSsz.Stock.Closure.index_memcpyStub.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Automation2.DomainRanges.

Import ListNotations.
Open Scope Z_scope.

(* The Level 1 contract of rlp_decode.txAccessList
   (sym_rlp_decode_txAccessList), review packet b1-tx.

   Calling convention (machine runs, hint pack): x10 = result pointer
   (24 bytes: slice pointer, slice length, u16 error code), x11 = pointer
   to the 16-byte std.mem.Allocator {ctx, vtable}, x12 = pointer to the
   16-byte `rest` slice {pointer, length}. The frame is 576 bytes. Below it
   lie the callee frames: decodeItem 16 bytes; keysEnsureCapacity 128 and
   keysToOwnedSlice / entriesToOwnedSlice 112, each including the 16-byte
   frame of the allocator entry it calls (AltFlAllocPremises.v,
   altFlCallStackBytes); the inlined alloc, remap and free calls of the
   entries list use 16; memcpy none. So 128 bytes.

   Allocator (AltFlAllocPremises.v, the array-list lane): the entry owns
   altFlHeap (the allocator's state), the Allocator object at x11
   (altFlAllocatorObject: ctx word, vtable word = sym_alt_fl_alloc_vtable)
   and the vtable cells (altFlVtable), and returns all three. A live block
   of n bytes is `p ↦ₘ∗ bytes ∗ altFlBlock p n log2Align`; the keys
   ([32]u8) use log2 alignment 0, the entries (input.AccessListEntry) 3.
   memcpy (ZiskMemcpyPremise.v) writes the ZisK scratch word, so the
   contract owns that word too.

   An entry of the returned slice is 40 bytes: keys slice pointer (+0),
   keys count (+8), address (+16, 20 bytes), 4 padding bytes (+36) that the
   code never writes (+0x460..+0x484): their value is whatever the
   allocator block held, so the contract leaves them existential. *)

Notation txAccessListFrameBytes := ((576) : Z) (only parsing).
Notation txAccessListCalleeBytes := ((128) : Z) (only parsing).
Notation txAccessListKeysLog2Align := ((0) : Z) (only parsing).
Notation txAccessListEntriesLog2Align := ((3) : Z) (only parsing).
Notation txAccessListScratchSize := ((8) : Z) (only parsing).
Notation txAccessListResultSize := ((24) : Z) (only parsing).
Notation txAccessListCellSize := ((16) : Z) (only parsing).
Notation txAccessListEntrySize := ((40) : Z) (only parsing).
Notation txAccessListKeySize := ((32) : Z) (only parsing).
Notation txAccessListPaddingSize := ((4) : Z) (only parsing).
Notation txAccessListInvalidBlockCode := ((3) : Z) (only parsing).
Notation txAccessListRamLow := ((0xa0000000) : Z) (only parsing).
Notation txAccessListRamHigh := ((0xc0000000) : Z) (only parsing).
Notation txAccessListInputBufferLow := ((2 ^ 30) : Z) (only parsing).
Notation txAccessListInputBufferHigh := ((2 ^ 31) : Z) (only parsing).

(* Register quantities are the register values themselves (F44). *)
Record TxAccessListArgs := {
  txResultPointer : bv 64;
  txAllocatorPointer : bv 64;
  txRestPointer : bv 64;
  txAllocatorContext : bv 64;
  txInputPointer : bv 64;
  txInputLength : bv 64;
  txInputBytes : list byte;
  txInputEnd : bv 64;
  txStackPointer : bv 64;
  txReturnAddress : bv 64;
  txSavedX8 : bv 64; txSavedX9 : bv 64;
  txSavedX18 : bv 64; txSavedX19 : bv 64; txSavedX20 : bv 64;
  txSavedX21 : bv 64; txSavedX22 : bv 64; txSavedX23 : bv 64;
  txSavedX24 : bv 64; txSavedX25 : bv 64; txSavedX26 : bv 64;
  txSavedX27 : bv 64;
  txScratchBefore : list byte
}.

(* Per returned entry: its keys slice pointer and its 4 padding bytes. *)
Record TxAccessListEntryImage := {
  imageKeysPointer : Z;
  imagePadding : list byte
}.

(* A heap block the function allocated and neither returned nor freed. *)
Record TxLeakedBlock := {
  leakedPointer : Z;
  leakedBytes : Z;
  leakedLog2Align : Z
}.

Record TxAccessListOutcome := {
  txOutcomeClass : TxAccessListOutcomeClass;
  txConsumed : Z;
  txResultBytes : list byte;
  txAfterFrame : list byte;
  txScratchAfter : list byte;
  txEntriesPointer : Z;
  txEntryImages : list TxAccessListEntryImage;
  (* Empty on success. *)
  txLeakedBlocks : list TxLeakedBlock
}.

Definition txRamRange (pointer length : Z) : Prop :=
  txAccessListRamLow <= pointer /\ 0 <= length /\
  pointer + length <= txAccessListRamHigh.

(* The plain ranges of the entry domain (exposed by the instance below). *)
Definition txAccessListArgsRanges (args : TxAccessListArgs) : Prop :=
  txAccessListRamLow <= bv_unsigned (txResultPointer args) /\
  bv_unsigned (txResultPointer args) + txAccessListResultSize <=
    txAccessListRamHigh /\
  txAccessListRamLow <= bv_unsigned (txAllocatorPointer args) /\
  bv_unsigned (txAllocatorPointer args) + txAccessListCellSize <=
    txAccessListRamHigh /\
  txAccessListRamLow <= bv_unsigned (txRestPointer args) /\
  bv_unsigned (txRestPointer args) + txAccessListCellSize <=
    txAccessListRamHigh /\
  txAccessListRamLow + txAccessListFrameBytes + txAccessListCalleeBytes <=
    bv_unsigned (txStackPointer args) /\
  bv_unsigned (txStackPointer args) <= txAccessListRamHigh /\
  bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
    bv_unsigned (txInputEnd args) /\
  ((txAccessListInputBufferLow <= bv_unsigned (txInputPointer args) /\
    bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
      txAccessListInputBufferHigh) \/
   (txAccessListRamLow <= bv_unsigned (txInputPointer args) /\
    bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
      txAccessListRamHigh)).

Definition txAccessListFrameBase (args : TxAccessListArgs) : Z :=
  bv_unsigned (txStackPointer args) - txAccessListFrameBytes.

Definition txAccessListCalleeBase (args : TxAccessListArgs) : Z :=
  bv_unsigned (txStackPointer args) - txAccessListFrameBytes -
    txAccessListCalleeBytes.

(* Each machine bound is a conjunct on bv_unsigned of a register or cell
   value (F44); the links to the meaning are separate conjuncts. *)
Definition txAccessListArgsWellFormed (args : TxAccessListArgs) : Prop :=
  txAccessListArgsRanges args /\
  Z.of_nat (List.length (txInputBytes args)) =
    bv_unsigned (txInputLength args) /\
  bv_unsigned (txStackPointer args) mod 16 = 0 /\
  bv_unsigned (txReturnAddress args) mod 4 = 0 /\
  Z.of_nat (List.length (txScratchBefore args)) = txAccessListScratchSize /\
  (* the six owned argument ranges are pairwise separate *)
  separateRanges (bv_unsigned (txResultPointer args)) txAccessListResultSize
    (bv_unsigned (txAllocatorPointer args)) txAccessListCellSize /\
  separateRanges (bv_unsigned (txResultPointer args)) txAccessListResultSize
    (bv_unsigned (txRestPointer args)) txAccessListCellSize /\
  separateRanges (bv_unsigned (txAllocatorPointer args)) txAccessListCellSize
    (bv_unsigned (txRestPointer args)) txAccessListCellSize /\
  separateRanges (bv_unsigned (txInputPointer args))
    (bv_unsigned (txInputLength args))
    (bv_unsigned (txResultPointer args)) txAccessListResultSize /\
  separateRanges (bv_unsigned (txInputPointer args))
    (bv_unsigned (txInputLength args))
    (bv_unsigned (txAllocatorPointer args)) txAccessListCellSize /\
  separateRanges (bv_unsigned (txInputPointer args))
    (bv_unsigned (txInputLength args))
    (bv_unsigned (txRestPointer args)) txAccessListCellSize /\
  separateRanges (txAccessListCalleeBase args)
    (txAccessListFrameBytes + txAccessListCalleeBytes)
    (bv_unsigned (txResultPointer args)) txAccessListResultSize /\
  separateRanges (txAccessListCalleeBase args)
    (txAccessListFrameBytes + txAccessListCalleeBytes)
    (bv_unsigned (txAllocatorPointer args)) txAccessListCellSize /\
  separateRanges (txAccessListCalleeBase args)
    (txAccessListFrameBytes + txAccessListCalleeBytes)
    (bv_unsigned (txRestPointer args)) txAccessListCellSize /\
  separateRanges (txAccessListCalleeBase args)
    (txAccessListFrameBytes + txAccessListCalleeBytes)
    (bv_unsigned (txInputPointer args)) (bv_unsigned (txInputLength args)) /\
  txAccessListDomain (txInputBytes args).

#[export] Instance txAccessListArgsWellFormedRanges (args : TxAccessListArgs) :
  ZesuDomainRanges (txAccessListArgsWellFormed args)
    (txAccessListArgsRanges args).
Proof. intros [Hranges _]. exact Hranges. Qed.

(* The 40-byte image of one returned entry. *)
Definition txAccessListEntryBytes (entry : AccessListEntryValue)
    (image : TxAccessListEntryImage) : list byte :=
  word64Bytes (imageKeysPointer image) ++
  word64Bytes (Z.of_nat (List.length (entryKeys entry))) ++
  entryAddress entry ++ imagePadding image.

Definition txAccessListEntriesBytes (entries : list AccessListEntryValue)
    (images : list TxAccessListEntryImage) : list byte :=
  concat (zip_with txAccessListEntryBytes entries images).

(* The result record: success writes pointer, length and a zero u16 code
   (+0x4fc..+0x504; bytes 18..23 keep their entry value); an error writes
   0, 0 and the 64-bit word 3 (+0x4a8..+0x4b4). *)
Definition txAccessListResultImage (outcome : TxAccessListOutcome) : Prop :=
  (List.length (txResultBytes outcome) = 24)%nat /\
  match txOutcomeClass outcome with
  | txAccessListOk entries =>
      word64At (txResultBytes outcome) 0 (txEntriesPointer outcome) /\
      word64At (txResultBytes outcome) 8 (Z.of_nat (List.length entries)) /\
      byteAt (txResultBytes outcome) 16 0 /\ byteAt (txResultBytes outcome) 17 0
  | txAccessListInvalidInput | txAccessListAllocationFailure =>
      txResultBytes outcome =
        word64Bytes 0 ++ word64Bytes 0 ++
        word64Bytes txAccessListInvalidBlockCode
  end.

(* Ranges and shape of the returned heap: every non-empty returned slice
   lies in RAM; a zero-length slice's pointer is not constrained (the
   empty std.ArrayList holds the alignment, 8, as its pointer). *)
Definition txAccessListHeapImage (outcome : TxAccessListOutcome) : Prop :=
  match txOutcomeClass outcome with
  | txAccessListOk entries =>
      List.length (txEntryImages outcome) = List.length entries /\
      txLeakedBlocks outcome = [] /\
      (entries <> [] ->
       txRamRange (txEntriesPointer outcome)
         (txAccessListEntrySize * Z.of_nat (List.length entries))) /\
      Forall2 (fun entry image =>
        Z.of_nat (List.length (imagePadding image)) = txAccessListPaddingSize /\
        (entryKeys entry <> [] ->
         txRamRange (imageKeysPointer image)
           (txAccessListKeySize * Z.of_nat (List.length (entryKeys entry)))))
        entries (txEntryImages outcome)
  | txAccessListInvalidInput | txAccessListAllocationFailure =>
      txEntryImages outcome = [] /\
      Forall (fun block =>
        0 < leakedBytes block /\
        txRamRange (leakedPointer block) (leakedBytes block) /\
        (leakedLog2Align block = txAccessListKeysLog2Align \/
         leakedLog2Align block = txAccessListEntriesLog2Align))
        (txLeakedBlocks outcome)
  end.

Definition txAccessListAllows (args : TxAccessListArgs)
    (outcome : TxAccessListOutcome) : Prop :=
  TxAccessListMeaningModuloKnownBugs (txInputBytes args)
    (txOutcomeClass outcome) (txConsumed outcome) /\
  txAccessListResultImage outcome /\
  txAccessListHeapImage outcome /\
  List.length (txAfterFrame outcome) = Z.to_nat txAccessListFrameBytes /\
  Z.of_nat (List.length (txScratchAfter outcome)) = txAccessListScratchSize.

Definition txAccessListSysRegs (args : TxAccessListArgs) :
    list (reg_kind * valu_shape) :=
  map (fun '(r, shape) =>
    (r, if decide (r = KindReg "zisk_input_end")
        then ExactShape (RVal_Bits (txInputEnd args))
        else shape)) zesu_sys_regs.

(* Plan B5: own map, the three array-list selected codes, decodeItem, the
   general memcpy premise and the allocator premises. *)
Definition txAccessListContractCode `{!islaG Sigma} `{!threadG}
    : iProp Sigma :=
  (txAccessListSelectedCode ∗ keysEnsureCapacitySelectedCode ∗
   keysToOwnedSliceSelectedCode ∗ entriesToOwnedSliceSelectedCode ∗
   decodeItemSelectedCode ∗ ziskMemcpyCallPremise ∗
   altFlAllocCallPremise ∗ altFlRemapCallPremise ∗ altFlFreeCallPremise)%I.

(* A returned slice: nothing when empty, else its bytes and its block. *)
Definition txOwnedSlice `{!islaG Sigma} `{!threadG}
    (pointer log2Align : Z) (bytes : list byte) : iProp Sigma :=
  (match bytes with
   | [] => True
   | _ :: _ => pointer ↦ₘ∗ bytes ∗
               altFlBlock pointer (Z.of_nat (List.length bytes)) log2Align
   end)%I.

Definition txAccessListReturnedHeap `{!islaG Sigma} `{!threadG}
    (outcome : TxAccessListOutcome) : iProp Sigma :=
  (match txOutcomeClass outcome with
   | txAccessListOk entries =>
       txOwnedSlice (txEntriesPointer outcome) txAccessListEntriesLog2Align
         (txAccessListEntriesBytes entries (txEntryImages outcome)) ∗
       [∗ list] entry; image ∈ entries; txEntryImages outcome,
         txOwnedSlice (imageKeysPointer image) txAccessListKeysLog2Align
           (concat (entryKeys entry))
   | txAccessListInvalidInput | txAccessListAllocationFailure => True
   end ∗
   (* error paths leak what they allocated: owned, contents unknown *)
   [∗ list] block ∈ txLeakedBlocks outcome,
     leakedPointer block ↦ₘ? leakedBytes block ∗
     altFlBlock (leakedPointer block) (leakedBytes block)
       (leakedLog2Align block))%I.

  Definition txAccessListEntryResources `{!islaG Sigma} `{!threadG}
      (args : TxAccessListArgs) : iProp Sigma :=
    (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
     reg_col (txAccessListSysRegs args) ∗
     "x1" ↦ᵣ RVal_Bits (txReturnAddress args) ∗
     "x2" ↦ᵣ RVal_Bits (txStackPointer args) ∗
     "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
     "x8" ↦ᵣ RVal_Bits (txSavedX8 args) ∗
     "x9" ↦ᵣ RVal_Bits (txSavedX9 args) ∗
     "x10" ↦ᵣ RVal_Bits (txResultPointer args) ∗
     "x11" ↦ᵣ RVal_Bits (txAllocatorPointer args) ∗
     "x12" ↦ᵣ RVal_Bits (txRestPointer args) ∗
     "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
     "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
     "x18" ↦ᵣ RVal_Bits (txSavedX18 args) ∗
     "x19" ↦ᵣ RVal_Bits (txSavedX19 args) ∗
     "x20" ↦ᵣ RVal_Bits (txSavedX20 args) ∗
     "x21" ↦ᵣ RVal_Bits (txSavedX21 args) ∗
     "x22" ↦ᵣ RVal_Bits (txSavedX22 args) ∗
     "x23" ↦ᵣ RVal_Bits (txSavedX23 args) ∗
     "x24" ↦ᵣ RVal_Bits (txSavedX24 args) ∗
     "x25" ↦ᵣ RVal_Bits (txSavedX25 args) ∗
     "x26" ↦ᵣ RVal_Bits (txSavedX26 args) ∗
     "x27" ↦ᵣ RVal_Bits (txSavedX27 args) ∗
     "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
     "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
     bv_unsigned (txInputPointer args) ↦ₘ∗ txInputBytes args ∗
     bv_unsigned (txRestPointer args) ↦ₘ∗
       (word64Bytes (bv_unsigned (txInputPointer args)) ++
        word64Bytes (bv_unsigned (txInputLength args))) ∗
     altFlAllocatorObject (bv_unsigned (txAllocatorPointer args))
       (bv_unsigned (txAllocatorContext args)) ∗
     altFlVtable ∗
     altFlHeap ∗
     ziskExtraParamsAddress ↦ₘ∗ txScratchBefore args ∗
     bv_unsigned (txResultPointer args) ↦ₘ? txAccessListResultSize ∗
     txAccessListFrameBase args ↦ₘ? txAccessListFrameBytes ∗
     txAccessListCalleeBase args ↦ₘ? txAccessListCalleeBytes ∗
     ⌜txAccessListArgsWellFormed args⌝ ∗ True)%I.

  (* Caller-saved registers return arbitrary; sp, ra (restored from the
     frame, +0x4b8) and the callee-saved registers are preserved. The ZisK
     system registers return with shape only (the memcpy and allocator
     premises do not fix them). *)
  Definition txAccessListExitResources `{!islaG Sigma} `{!threadG}
      (args : TxAccessListArgs) (outcome : TxAccessListOutcome) : iProp Sigma :=
    (∃ (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
     reg_col zesu_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (txReturnAddress args) ∗
     "x2" ↦ᵣ RVal_Bits (txStackPointer args) ∗
     "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
     "x8" ↦ᵣ RVal_Bits (txSavedX8 args) ∗
     "x9" ↦ᵣ RVal_Bits (txSavedX9 args) ∗
     "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
     "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
     "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
     "x18" ↦ᵣ RVal_Bits (txSavedX18 args) ∗
     "x19" ↦ᵣ RVal_Bits (txSavedX19 args) ∗
     "x20" ↦ᵣ RVal_Bits (txSavedX20 args) ∗
     "x21" ↦ᵣ RVal_Bits (txSavedX21 args) ∗
     "x22" ↦ᵣ RVal_Bits (txSavedX22 args) ∗
     "x23" ↦ᵣ RVal_Bits (txSavedX23 args) ∗
     "x24" ↦ᵣ RVal_Bits (txSavedX24 args) ∗
     "x25" ↦ᵣ RVal_Bits (txSavedX25 args) ∗
     "x26" ↦ᵣ RVal_Bits (txSavedX26 args) ∗
     "x27" ↦ᵣ RVal_Bits (txSavedX27 args) ∗
     "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
     "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
     bv_unsigned (txInputPointer args) ↦ₘ∗ txInputBytes args ∗
     bv_unsigned (txRestPointer args) ↦ₘ∗
       (word64Bytes (bv_unsigned (txInputPointer args) + txConsumed outcome) ++
        word64Bytes (bv_unsigned (txInputLength args) - txConsumed outcome)) ∗
     altFlAllocatorObject (bv_unsigned (txAllocatorPointer args))
       (bv_unsigned (txAllocatorContext args)) ∗
     altFlVtable ∗
     altFlHeap ∗
     ziskExtraParamsAddress ↦ₘ∗ txScratchAfter outcome ∗
     bv_unsigned (txResultPointer args) ↦ₘ∗ txResultBytes outcome ∗
     txAccessListFrameBase args ↦ₘ∗ txAfterFrame outcome ∗
     txAccessListCalleeBase args ↦ₘ? txAccessListCalleeBytes ∗
     txAccessListReturnedHeap outcome ∗ True)%I.

  Definition txAccessListContractResources `{!islaG Sigma} `{!threadG}
      (returnAddress : Z) :
      IslarisContractResources TxAccessListArgs TxAccessListOutcome :=
    {| islarisCode := txAccessListContractCode;
       islarisEntry := fun args =>
         (⌜bv_unsigned (txReturnAddress args) = returnAddress⌝ ∗
          txAccessListEntryResources args)%I;
       islarisExit := txAccessListExitResources |}.

  Definition txAccessListContractModel (returnAddress : Z) :
      IslarisContractModel TxAccessListArgs TxAccessListOutcome :=
    {| islarisContractAllows := fun args outcome =>
         bv_unsigned (txReturnAddress args) = returnAddress /\
         txAccessListAllows args outcome;
       islarisContractStep := fun source target =>
         ZesuSsz.Stock.Closure.index_txAccessList.txAccessList_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_ensureTotalCapacity.ensureTotalCapacity_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_sliceBytes32.sliceBytes32_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_sliceAccessList.sliceAccessList_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_allocatorAlloc.allocatorAlloc_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_allocatorRemap.allocatorRemap_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_allocatorFree.allocatorFree_cfg_step
           source target \/
         ZesuSsz.Stock.Closure.index_memcpyStub.memcpyStub_cfg_step
           source target;
       islarisContractResources := fun Sigma HG HT =>
         @txAccessListContractResources Sigma HG HT returnAddress |}.

  (* This declaration states the native proof objective. It does not prove it. *)
  Definition TxAccessListContractCorrect : Prop :=
    forall returnAddress,
      IslarisContractCorrect sym_rlp_decode_txAccessList returnAddress
        (txAccessListContractModel returnAddress).
