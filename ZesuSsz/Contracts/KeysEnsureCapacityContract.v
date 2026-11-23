From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Automation2.DomainRanges.
Require ZesuSsz.Stock.Closure.index_ensureTotalCapacity.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* array_list.Aligned([32]u8,null).ensureTotalCapacity(self: *List,
   gpa: Allocator, new_capacity: usize) Allocator.Error!void.
   a0 = list, a1 = allocator, a2 = new_capacity; the error code returns in
   a0 (0 or 2 = OutOfMemory). *)

(* Own frame 112 bytes, plus the 16-byte frame of an allocator callee. *)
Notation keysEnsureCapacityStackBytes := ((112 + 16) : Z) (only parsing).
(* The requested capacity is a count bounded by the input; the bound keeps
   the grown byte size below altFlMaxRequestBytes. *)
Notation keysEnsureCapacityMaxRequest := ((2 ^ 32) : Z) (only parsing).

(* Zig's growth rule for a capacity below the request (no saturation under
   the request bound). *)
Definition arrayListGrownCapacity (requested : Z) : Z :=
  requested + requested / 2 + 2.

Record EnsureCapacityArgs : Type := {
  ensureListPointer : bv 64;
  ensureAllocatorPointer : bv 64;
  ensureAllocatorContext : Z;
  ensureList : ArrayListState;
  ensureRequested : bv 64;
  ensureScratchBefore : list byte;
  ensureStackPointer : bv 64;
  ensureReturnAddress : bv 64;
  ensureSaved : ArrayListCalleeSaved
}.

Record EnsureCapacityOutcome : Type := {
  ensureKind : ArrayListOutcomeKind;
  ensureListAfter : ArrayListState
}.

Definition keysEnsureCapacityDomain (args : EnsureCapacityArgs) : Prop :=
  arrayListWellFormed keysElementBytes (ensureList args) /\
  arrayListRamRange (bv_unsigned (ensureListPointer args)) arrayListHeaderSize /\
  (8 | bv_unsigned (ensureListPointer args)) /\
  arrayListRamRange (bv_unsigned (ensureAllocatorPointer args)) arrayListAllocatorSize /\
  (8 | bv_unsigned (ensureAllocatorPointer args)) /\
  0 <= ensureAllocatorContext args < 2 ^ 64 /\
  bv_unsigned (ensureRequested args) < keysEnsureCapacityMaxRequest /\
  Z.of_nat (length (ensureScratchBefore args)) = arrayListScratchSize /\
  arrayListStackLayout (bv_unsigned (ensureStackPointer args)) keysEnsureCapacityStackBytes /\
  (4 | bv_unsigned (ensureReturnAddress args)).

(* The machine code with alt_fl_alloc, whose remap always fails: a request
   within the capacity changes nothing; otherwise alloc the grown capacity:
   on null return OutOfMemory and keep the list; else copy the items, free
   the old buffer (when it has capacity), and set pointer and capacity. *)
Definition keysEnsureCapacityAllows (args : EnsureCapacityArgs)
    (outcome : EnsureCapacityOutcome) : Prop :=
  let state := ensureList args in
  arrayListWellFormed keysElementBytes (ensureListAfter outcome) /\
  (if bv_unsigned (ensureRequested args) <=? arrayListCapacity state then
     ensureKind outcome = arrayListSuccess /\ ensureListAfter outcome = state
   else
     match ensureKind outcome with
     | arrayListSuccess =>
         arrayListLength (ensureListAfter outcome) = arrayListLength state /\
         arrayListCapacity (ensureListAfter outcome) =
           arrayListGrownCapacity (bv_unsigned (ensureRequested args)) /\
         arrayListItems (ensureListAfter outcome) = arrayListItems state
     | arrayListOutOfMemory => ensureListAfter outcome = state
     end).

(* The ZisK memcpy scratch word (ziskExtraParamsAddress) after the call:
   the count of the one copy on the growing success path, its entry bytes
   otherwise. *)
Definition keysEnsureCapacityScratchAfter (args : EnsureCapacityArgs)
    (outcome : EnsureCapacityOutcome) : list byte :=
  if bv_unsigned (ensureRequested args) <=? arrayListCapacity (ensureList args)
  then ensureScratchBefore args
  else
    match ensureKind outcome with
    | arrayListSuccess =>
        word64Bytes (arrayListLength (ensureList args) * keysElementBytes)
    | arrayListOutOfMemory => ensureScratchBefore args
    end.

Definition keysEnsureCapacityEntry `{!islaG Sigma} `{!threadG}
    (args : EnsureCapacityArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (ensureReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (ensureStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x10" ↦ᵣ RVal_Bits (ensureListPointer args) ∗
   "x11" ↦ᵣ RVal_Bits (ensureAllocatorPointer args) ∗
   "x12" ↦ᵣ RVal_Bits (ensureRequested args) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   arrayListSavedRegisters (ensureSaved args) ∗
   bv_unsigned (ensureListPointer args) ↦ₘ∗ arrayListHeaderBytes (ensureList args) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (ensureList args) ∗
   ziskExtraParamsAddress ↦ₘ∗ ensureScratchBefore args ∗
   altFlAllocatorObject (bv_unsigned (ensureAllocatorPointer args))
     (ensureAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (bv_unsigned (ensureStackPointer args) - keysEnsureCapacityStackBytes) ↦ₘ?
     keysEnsureCapacityStackBytes ∗
   ⌜keysEnsureCapacityDomain args⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@keysEnsureCapacityEntry) := I.
Global Typeclasses Opaque keysEnsureCapacityEntry.

Definition keysEnsureCapacityExit `{!islaG Sigma} `{!threadG}
    (args : EnsureCapacityArgs) (outcome : EnsureCapacityOutcome) :
    iProp Sigma :=
  (∃ (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (ensureReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (ensureStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   arrayListSavedRegisters (ensureSaved args) ∗
   bv_unsigned (ensureListPointer args) ↦ₘ∗ arrayListHeaderBytes (ensureListAfter outcome) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (ensureListAfter outcome) ∗
   ziskExtraParamsAddress ↦ₘ∗ keysEnsureCapacityScratchAfter args outcome ∗
   altFlAllocatorObject (bv_unsigned (ensureAllocatorPointer args))
     (ensureAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (bv_unsigned (ensureStackPointer args) - keysEnsureCapacityStackBytes) ↦ₘ?
     keysEnsureCapacityStackBytes ∗
   ⌜bv_unsigned x10 = arrayListOutcomeCode (ensureKind outcome)⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@keysEnsureCapacityExit) := I.
Global Typeclasses Opaque keysEnsureCapacityExit.

(* The selected code is the own map only. The allocator and memcpy entries
   are trusted premises (AltFlAllocPremises.v, ZiskMemcpyPremise.v). *)
Definition keysEnsureCapacityContractCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (keysEnsureCapacitySelectedCode ∗ altFlAllocatorPremises ∗
   ziskMemcpyCallPremise)%I.
Global Instance : LithiumUnfold (@keysEnsureCapacityContractCode) := I.
Global Typeclasses Opaque keysEnsureCapacityContractCode.

Definition keysEnsureCapacityResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources EnsureCapacityArgs EnsureCapacityOutcome :=
  {| islarisCode := keysEnsureCapacityContractCode;
     islarisEntry := fun args =>
       (⌜bv_unsigned (ensureReturnAddress args) = returnAddress⌝ ∗
        keysEnsureCapacityEntry args)%I;
     islarisExit := keysEnsureCapacityExit |}.

Definition keysEnsureCapacityContractModel (returnAddress : Z) :
    IslarisContractModel EnsureCapacityArgs EnsureCapacityOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (ensureReturnAddress args) = returnAddress /\
       keysEnsureCapacityDomain args /\
       keysEnsureCapacityAllows args outcome;
     islarisContractStep :=
       ZesuSsz.Stock.Closure.index_ensureTotalCapacity.ensureTotalCapacity_cfg_step;
     islarisContractResources := fun Sigma HG HT =>
       @keysEnsureCapacityResources Sigma HG HT returnAddress |}.

(* This declaration states the native proof objective. It does not prove it. *)
Definition KeysEnsureCapacityContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_32_u8_null_ensureTotalCapacity
      returnAddress (keysEnsureCapacityContractModel returnAddress).

(* The ranges and links of the folded domain as plain facts. *)
Lemma keysEnsureCapacityDomainRanges (args : EnsureCapacityArgs) :
  keysEnsureCapacityDomain args ->
  0 <= arrayListLength (ensureList args) <=
    arrayListCapacity (ensureList args) /\
  Z.of_nat (length (arrayListItems (ensureList args))) =
    arrayListLength (ensureList args) * keysElementBytes /\
  0 < arrayListPointer (ensureList args) < 2 ^ 64 /\
  (0 < arrayListCapacity (ensureList args) ->
    mapRamBase defaultMap <= arrayListPointer (ensureList args) /\
    arrayListPointer (ensureList args) +
      arrayListCapacity (ensureList args) * keysElementBytes <=
      machineRamEnd defaultMap) /\
  mapRamBase defaultMap <= bv_unsigned (ensureListPointer args) /\
  bv_unsigned (ensureListPointer args) + arrayListHeaderSize <= machineRamEnd defaultMap /\
  (8 | bv_unsigned (ensureListPointer args)) /\
  mapRamBase defaultMap <= bv_unsigned (ensureAllocatorPointer args) /\
  bv_unsigned (ensureAllocatorPointer args) + arrayListAllocatorSize <=
    machineRamEnd defaultMap /\
  (8 | bv_unsigned (ensureAllocatorPointer args)) /\
  0 <= ensureAllocatorContext args < 2 ^ 64 /\
  bv_unsigned (ensureRequested args) < keysEnsureCapacityMaxRequest /\
  Z.of_nat (length (ensureScratchBefore args)) = arrayListScratchSize /\
  (16 | bv_unsigned (ensureStackPointer args)) /\
  mapRamBase defaultMap <=
    bv_unsigned (ensureStackPointer args) - keysEnsureCapacityStackBytes /\
  bv_unsigned (ensureStackPointer args) <= machineRamEnd defaultMap /\
  (4 | bv_unsigned (ensureReturnAddress args)).
Proof.
  unfold keysEnsureCapacityDomain, arrayListWellFormed, arrayListRamRange,
    arrayListStackLayout.
  tauto.
Qed.

#[export] Instance keysEnsureCapacityDomainRangesInstance
    (args : EnsureCapacityArgs) :
  ZesuDomainRanges (keysEnsureCapacityDomain args) _ :=
  keysEnsureCapacityDomainRanges args.
