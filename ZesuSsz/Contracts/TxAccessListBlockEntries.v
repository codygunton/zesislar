From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Open Scope Z_scope.

(* The block-entry form of the txAccessList contract (TxAccessListContract.v)
   that the generator reads (tools/block/functions/entry_interface_inputs.py):
   the same arguments; the allocator object and the vtable spelled as their
   bytes (altFlAllocatorObject, altFlVtable); the uninitialised 576-byte frame
   split at the prologue's saved-register area (ra, s0, s1, s2..s11: the top
   104 bytes) so that the frame row names its slots. The composition proves
   txAccessListEntryResources from this form and back. *)
Notation txBlockSavedBytes := ((104) : Z) (only parsing).
Notation txBlockLocalBytes := ((472) : Z) (only parsing).

Definition txAccessListBlockDomainAt (returnAddress : Z) (args : TxAccessListArgs) : Prop :=
  bv_unsigned (txReturnAddress args) = returnAddress /\ txAccessListArgsWellFormed args.

Definition txAccessListBlockEntryResources `{!islaG Sigma} `{!threadG}
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
   bv_unsigned (txAllocatorPointer args) ↦ₘ∗
     altFlAllocatorBytes (bv_unsigned (txAllocatorContext args)) ∗
   sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes ∗
   altFlHeap ∗
   ziskExtraParamsAddress ↦ₘ∗ txScratchBefore args ∗
   bv_unsigned (txResultPointer args) ↦ₘ? txAccessListResultSize ∗
   txAccessListFrameBase args ↦ₘ? txBlockLocalBytes ∗
   (bv_unsigned (txStackPointer args) - txBlockSavedBytes) ↦ₘ? txBlockSavedBytes ∗
   txAccessListCalleeBase args ↦ₘ? txAccessListCalleeBytes ∗
   ⌜txAccessListArgsWellFormed args⌝ ∗ True)%I.

Global Typeclasses Opaque txAccessListBlockEntryResources.
Global Instance : LithiumUnfold (@txAccessListBlockEntryResources) := I.
