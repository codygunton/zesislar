From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
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

(* The little-endian word of a byte list at an offset (the word-link reader of
   entry_interface_inputs.py). *)
Definition txBlockWord (bytes : list byte) (offset : Z) : Z :=
  little_endian_to_bv 8 (take 8 (drop (Z.to_nat offset) bytes)).

Definition txBlockRestBytes (args : TxAccessListArgs) : list byte :=
  word64Bytes (bv_unsigned (txInputPointer args)) ++
  word64Bytes (bv_unsigned (txInputLength args)).

(* txAccessListArgsWellFormed with its ranges written out, so that the
   generator reads each conjunct (entry_interface_inputs.py reads the body of
   the well-formedness predicate of this file), followed by the lengths and
   word links of the owned cells the code loads from (`rest`, the allocator
   object, the vtable). It implies the contract's predicate
   (txAccessListBlockArgsWellFormed_contract); the converse holds since the
   added conjuncts are byte-level identities. *)
Definition txAccessListBlockArgsWellFormed (args : TxAccessListArgs) : Prop :=
  0xa0000000 <= bv_unsigned (txResultPointer args) /\
  bv_unsigned (txResultPointer args) + 24 <= 0xc0000000 /\
  0xa0000000 <= bv_unsigned (txAllocatorPointer args) /\
  bv_unsigned (txAllocatorPointer args) + 16 <= 0xc0000000 /\
  (8 | bv_unsigned (txAllocatorPointer args)) /\
  0xa0000000 <= bv_unsigned (txRestPointer args) /\
  bv_unsigned (txRestPointer args) + 16 <= 0xc0000000 /\
  0xa0000000 + 576 + 128 <= bv_unsigned (txStackPointer args) /\
  bv_unsigned (txStackPointer args) <= 0xc0000000 /\
  bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
    bv_unsigned (txInputEnd args) /\
  ((2 ^ 30 <= bv_unsigned (txInputPointer args) /\
    bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <= 2 ^ 31) \/
   (0xa0000000 <= bv_unsigned (txInputPointer args) /\
    bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <= 0xc0000000)) /\
  Z.of_nat (List.length (txInputBytes args)) = bv_unsigned (txInputLength args) /\
  bv_unsigned (txStackPointer args) mod 16 = 0 /\
  bv_unsigned (txReturnAddress args) mod 4 = 0 /\
  Z.of_nat (List.length (txScratchBefore args)) = 8 /\
  separateRanges (bv_unsigned (txResultPointer args)) 24
    (bv_unsigned (txAllocatorPointer args)) 16 /\
  separateRanges (bv_unsigned (txResultPointer args)) 24
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (bv_unsigned (txAllocatorPointer args)) 16
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (bv_unsigned (txInputPointer args)) (bv_unsigned (txInputLength args))
    (bv_unsigned (txResultPointer args)) 24 /\
  separateRanges (bv_unsigned (txInputPointer args)) (bv_unsigned (txInputLength args))
    (bv_unsigned (txAllocatorPointer args)) 16 /\
  separateRanges (bv_unsigned (txInputPointer args)) (bv_unsigned (txInputLength args))
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (bv_unsigned (txStackPointer args) - 576 - 128) (576 + 128)
    (bv_unsigned (txResultPointer args)) 24 /\
  separateRanges (bv_unsigned (txStackPointer args) - 576 - 128) (576 + 128)
    (bv_unsigned (txAllocatorPointer args)) 16 /\
  separateRanges (bv_unsigned (txStackPointer args) - 576 - 128) (576 + 128)
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (bv_unsigned (txStackPointer args) - 576 - 128) (576 + 128)
    (bv_unsigned (txInputPointer args)) (bv_unsigned (txInputLength args)) /\
  txAccessListDomain (txInputBytes args) /\
  length (txBlockRestBytes args) = 16%nat /\
  length (altFlAllocatorBytes (bv_unsigned (txAllocatorContext args))) = 16%nat /\
  length altFlVtableBytes = 32%nat /\
  txBlockWord (txBlockRestBytes args) 0 = bv_unsigned (txInputPointer args) /\
  txBlockWord (txBlockRestBytes args) 8 = bv_unsigned (txInputLength args) /\
  txBlockWord (altFlAllocatorBytes (bv_unsigned (txAllocatorContext args))) 0 =
    bv_unsigned (txAllocatorContext args) /\
  txBlockWord (altFlAllocatorBytes (bv_unsigned (txAllocatorContext args))) 8 =
    sym_alt_fl_alloc_vtable /\
  txBlockWord altFlVtableBytes 0 = sym_alt_fl_alloc_alloc /\
  txBlockWord altFlVtableBytes 16 = sym_alt_fl_alloc_remap /\
  txBlockWord altFlVtableBytes 24 = sym_alt_fl_alloc_free.

Lemma txAccessListBlockArgsWellFormed_contract (args : TxAccessListArgs) :
  txAccessListBlockArgsWellFormed args -> txAccessListArgsWellFormed args.
Proof.
  unfold txAccessListBlockArgsWellFormed, txAccessListArgsWellFormed,
    txAccessListArgsRanges, txAccessListFrameBase, txAccessListCalleeBase.
  tauto.
Qed.

Definition txAccessListBlockDomainAt (returnAddress : Z) (args : TxAccessListArgs) : Prop :=
  bv_unsigned (txReturnAddress args) = returnAddress /\ txAccessListBlockArgsWellFormed args.

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
   bv_unsigned (txRestPointer args) ↦ₘ∗ txBlockRestBytes args ∗
   bv_unsigned (txAllocatorPointer args) ↦ₘ∗
     altFlAllocatorBytes (bv_unsigned (txAllocatorContext args)) ∗
   sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes ∗
   altFlHeap ∗
   ziskExtraParamsAddress ↦ₘ∗ txScratchBefore args ∗
   bv_unsigned (txResultPointer args) ↦ₘ? 24 ∗
   (bv_unsigned (txStackPointer args) - 576) ↦ₘ? txBlockLocalBytes ∗
   (bv_unsigned (txStackPointer args) - txBlockSavedBytes) ↦ₘ? txBlockSavedBytes ∗
   (bv_unsigned (txStackPointer args) - 576 - 128) ↦ₘ? 128 ∗
   ⌜txAccessListBlockArgsWellFormed args⌝ ∗ True)%I.

Global Typeclasses Opaque txAccessListBlockEntryResources.
Global Instance : LithiumUnfold (@txAccessListBlockEntryResources) := I.

(* The keys slices of the entries finished so far (the outer loop cut owns
   them): the shape txAccessListReturnedHeap gives them on success. A name
   for the big separating conjunction, which the generator's expression
   check does not accept as text. *)
Definition txAccessListKeysSlices `{!islaG Sigma} `{!threadG}
    (done : list AccessListEntryValue) (images : list TxAccessListEntryImage) : iProp Sigma :=
  ([∗ list] entry; image ∈ done; images,
     txOwnedSlice (imageKeysPointer image) txAccessListKeysLog2Align (concat (entryKeys entry)))%I.
