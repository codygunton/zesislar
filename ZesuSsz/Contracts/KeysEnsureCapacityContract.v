From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
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
  ensureListPointer : Z;
  ensureAllocatorPointer : Z;
  ensureAllocatorContext : Z;
  ensureList : ArrayListState;
  ensureRequested : Z;
  ensureStackPointer : Z;
  ensureReturnAddress : Z;
  ensureSaved : list (bv 64)
}.

Record EnsureCapacityOutcome : Type := {
  ensureKind : ArrayListOutcomeKind;
  ensureListAfter : ArrayListState
}.

Definition keysEnsureCapacityDomain (args : EnsureCapacityArgs) : Prop :=
  arrayListWellFormed keysElementBytes (ensureList args) /\
  arrayListRamRange (ensureListPointer args) arrayListHeaderSize /\
  (8 | ensureListPointer args) /\
  arrayListRamRange (ensureAllocatorPointer args) arrayListAllocatorSize /\
  (8 | ensureAllocatorPointer args) /\
  0 <= ensureAllocatorContext args < 2 ^ 64 /\
  0 <= ensureRequested args < keysEnsureCapacityMaxRequest /\
  arrayListStackLayout (ensureStackPointer args) keysEnsureCapacityStackBytes /\
  0 <= ensureReturnAddress args < 2 ^ 64 /\
  (4 | ensureReturnAddress args) /\
  length (ensureSaved args) = 12%nat.

(* The machine code with alt_fl_alloc, whose remap always fails: a request
   within the capacity changes nothing; otherwise alloc the grown capacity:
   on null return OutOfMemory and keep the list; else copy the items, free
   the old buffer (when it has capacity), and set pointer and capacity. *)
Definition keysEnsureCapacityAllows (args : EnsureCapacityArgs)
    (outcome : EnsureCapacityOutcome) : Prop :=
  let state := ensureList args in
  arrayListWellFormed keysElementBytes (ensureListAfter outcome) /\
  (if ensureRequested args <=? arrayListCapacity state then
     ensureKind outcome = arrayListSuccess /\ ensureListAfter outcome = state
   else
     match ensureKind outcome with
     | arrayListSuccess =>
         arrayListLength (ensureListAfter outcome) = arrayListLength state /\
         arrayListCapacity (ensureListAfter outcome) =
           arrayListGrownCapacity (ensureRequested args) /\
         arrayListItems (ensureListAfter outcome) = arrayListItems state
     | arrayListOutOfMemory => ensureListAfter outcome = state
     end).

Definition keysEnsureCapacityEntry `{!islaG Sigma} `{!threadG}
    (args : EnsureCapacityArgs) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (ensureReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (ensureStackPointer args)) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (ensureListPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (ensureAllocatorPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (ensureRequested args)) ∗
   arrayListSavedRegisters (ensureSaved args) ∗
   arrayListAnyRegisters arrayListEntryScratch ∗
   ensureListPointer args ↦ₘ∗ arrayListHeaderBytes (ensureList args) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (ensureList args) ∗
   altFlAllocatorObject (ensureAllocatorPointer args)
     (ensureAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (ensureStackPointer args - keysEnsureCapacityStackBytes) ↦ₘ?
     keysEnsureCapacityStackBytes ∗
   ⌜keysEnsureCapacityDomain args⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@keysEnsureCapacityEntry) := I.
Global Typeclasses Opaque keysEnsureCapacityEntry.

Definition keysEnsureCapacityExit `{!islaG Sigma} `{!threadG}
    (args : EnsureCapacityArgs) (outcome : EnsureCapacityOutcome) :
    iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (ensureReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (ensureStackPointer args)) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (arrayListOutcomeCode (ensureKind outcome))) ∗
   arrayListSavedRegisters (ensureSaved args) ∗
   arrayListAnyRegisters arrayListExitScratch ∗
   ensureListPointer args ↦ₘ∗ arrayListHeaderBytes (ensureListAfter outcome) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (ensureListAfter outcome) ∗
   altFlAllocatorObject (ensureAllocatorPointer args)
     (ensureAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (ensureStackPointer args - keysEnsureCapacityStackBytes) ↦ₘ?
     keysEnsureCapacityStackBytes ∗ True)%I.
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
       (⌜ensureReturnAddress args = returnAddress⌝ ∗
        keysEnsureCapacityEntry args)%I;
     islarisExit := keysEnsureCapacityExit |}.

Definition keysEnsureCapacityContractModel (returnAddress : Z) :
    IslarisContractModel EnsureCapacityArgs EnsureCapacityOutcome :=
  {| islarisContractAllows := fun args outcome =>
       ensureReturnAddress args = returnAddress /\
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
  mapRamBase defaultMap <= ensureListPointer args /\
  ensureListPointer args + arrayListHeaderSize <= machineRamEnd defaultMap /\
  (8 | ensureListPointer args) /\
  mapRamBase defaultMap <= ensureAllocatorPointer args /\
  ensureAllocatorPointer args + arrayListAllocatorSize <=
    machineRamEnd defaultMap /\
  (8 | ensureAllocatorPointer args) /\
  0 <= ensureAllocatorContext args < 2 ^ 64 /\
  0 <= ensureRequested args < keysEnsureCapacityMaxRequest /\
  (16 | ensureStackPointer args) /\
  mapRamBase defaultMap <=
    ensureStackPointer args - keysEnsureCapacityStackBytes /\
  ensureStackPointer args <= machineRamEnd defaultMap /\
  0 <= ensureReturnAddress args < 2 ^ 64 /\
  (4 | ensureReturnAddress args) /\
  length (ensureSaved args) = 12%nat.
Proof.
  unfold keysEnsureCapacityDomain, arrayListWellFormed, arrayListRamRange,
    arrayListStackLayout.
  tauto.
Qed.

#[export] Instance keysEnsureCapacityDomainRangesInstance
    (args : EnsureCapacityArgs) :
  ZesuDomainRanges (keysEnsureCapacityDomain args) _ :=
  keysEnsureCapacityDomainRanges args.
