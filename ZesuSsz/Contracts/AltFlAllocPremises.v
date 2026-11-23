From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* Trusted premises for the allocator alt_fl_alloc, reached by jalr through
   the slots of alt_fl_alloc.vtable (alloc +0, resize +8, remap +16, free +24;
   ZesuSsz/Evidence/generate_zesu_cfg.py). Each premise has the form of
   memcpyCallPremise: the allocator entry satisfies a machine_call spec.

   The allocator state (altFlHeap) is a resource that callers thread through:
   the merged state/free-list object at sym_alt_fl_alloc_state (the address
   AltFlFree.v names freeListsPointer), the heap words ZKVM_HEAP_POS and
   ZKVM_HEAP_TOP (mapHeapPosAddress, mapHeapTopAddress), the unallocated bump
   region [pos, top), and every block on a free list. A block handed out by
   alloc is the caller's memory plus a token (altFlBlock) that owns its
   size-class slack; free takes both back. *)

Notation altFlCallStackBytes := ((16) : Z) (only parsing).
Notation altFlMaxLog2Alignment := ((3) : Z) (only parsing).
Notation altFlMaxRequestBytes := ((2 ^ 63) : Z) (only parsing).
(* The bump position stays at most 2^63: with requests below 2^63 the
   64-bit add of alloc's capacity check (pos + size) then cannot wrap. *)
Notation altFlMaxHeapPos := ((2 ^ 63) : Z) (only parsing).

(* The state object is the one free (AltFlFree.v) owns. *)
Lemma altFlStateIsFreeLists : sym_alt_fl_alloc_state = freeListsPointer.
Proof. reflexivity. Qed.

(* Size classes: class c < freeListCount holds blocks of 2^(c+3) bytes. The
   class of a request is freeSizeClass of AltFlFree.v, the class free uses. *)
Definition altFlClassBytes (class : Z) : Z := 2 ^ (class + 3).

Definition altFlListHead (lists : list byte) (class : Z) : Z :=
  littleEndian (firstn 8 (skipn (Z.to_nat (8 + 8 * class)) lists)).

Definition altFlChainHead (blocks : list Z) : Z :=
  match blocks with
  | [] => 0
  | block :: _ => block
  end.

Definition altFlChainBlockFacts (blockBytes block : Z) : Prop :=
  mapRamBase defaultMap <= block /\
  block + blockBytes <= machineRamEnd defaultMap /\
  (blockBytes | block).

(* One free list: each block owns its whole class size and stores the next
   block (0 at the end) in its first word. *)
Fixpoint altFlChain `{!islaG Sigma} `{!threadG}
    (blockBytes head : Z) (blocks : list Z) : iProp Sigma :=
  match blocks with
  | [] => ⌜head = 0⌝
  | block :: rest =>
      ⌜head = block /\ altFlChainBlockFacts blockBytes block⌝ ∗
      block ↦ₘ∗ word64Bytes (altFlChainHead rest) ∗
      (block + 8) ↦ₘ? (blockBytes - 8) ∗
      altFlChain blockBytes (altFlChainHead rest) rest
  end%I.

Record AltFlHeapState : Type := {
  altFlLists : list byte;
  altFlChains : list (list Z);
  altFlHeapPos : Z;
  altFlHeapTop : Z
}.

Definition altFlHeapWellFormed (heap : AltFlHeapState) : Prop :=
  Z.of_nat (length (altFlLists heap)) = freeListsBytes /\
  Z.of_nat (length (altFlChains heap)) = freeListCount /\
  0 <= altFlHeapPos heap <= altFlMaxHeapPos /\
  0 <= altFlHeapTop heap < 2 ^ 64 /\
  (altFlHeapPos heap < altFlHeapTop heap ->
    mapRamBase defaultMap <= altFlHeapPos heap /\
    altFlHeapTop heap <= machineRamEnd defaultMap).

Definition altFlHeapAt `{!islaG Sigma} `{!threadG}
    (heap : AltFlHeapState) : iProp Sigma :=
  (sym_alt_fl_alloc_state ↦ₘ∗ altFlLists heap ∗
   mapHeapPosAddress defaultMap ↦ₘ∗ word64Bytes (altFlHeapPos heap) ∗
   mapHeapTopAddress defaultMap ↦ₘ∗ word64Bytes (altFlHeapTop heap) ∗
   altFlHeapPos heap ↦ₘ? Z.max 0 (altFlHeapTop heap - altFlHeapPos heap) ∗
   ([∗ list] class ↦ blocks ∈ altFlChains heap,
      altFlChain (altFlClassBytes (Z.of_nat class))
        (altFlListHead (altFlLists heap) (Z.of_nat class)) blocks))%I.

Lemma altFlHeapAt_unfold `{!islaG Sigma} `{!threadG} (heap : AltFlHeapState) :
  altFlHeapAt heap ⊣⊢
  (sym_alt_fl_alloc_state ↦ₘ∗ altFlLists heap ∗
   mapHeapPosAddress defaultMap ↦ₘ∗ word64Bytes (altFlHeapPos heap) ∗
   mapHeapTopAddress defaultMap ↦ₘ∗ word64Bytes (altFlHeapTop heap) ∗
   altFlHeapPos heap ↦ₘ? Z.max 0 (altFlHeapTop heap - altFlHeapPos heap) ∗
   ([∗ list] class ↦ blocks ∈ altFlChains heap,
      altFlChain (altFlClassBytes (Z.of_nat class))
        (altFlListHead (altFlLists heap) (Z.of_nat class)) blocks))%I.
Proof. reflexivity. Qed.
Global Opaque altFlHeapAt.

(* The allocator state a caller owns between allocator calls. *)
Definition altFlHeap `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ heap : AltFlHeapState, altFlHeapAt heap ∗ ⌜altFlHeapWellFormed heap⌝)%I.

Lemma altFlHeap_unfold `{!islaG Sigma} `{!threadG} :
  altFlHeap ⊣⊢
  (∃ heap : AltFlHeapState, altFlHeapAt heap ∗ ⌜altFlHeapWellFormed heap⌝)%I.
Proof. reflexivity. Qed.
Global Opaque altFlHeap.

(* A live block of `bytes` bytes at `pointer`, allocated with alignment
   2^log2Align. Its class slack (the rest of the class-size block) belongs to
   the token; a large block (class >= freeListCount) has no slack. A
   zero-byte block owns nothing. *)
Definition altFlBlockSlack (bytes log2Align : Z) : Z :=
  if bytes =? 0 then 0
  else if freeSizeClass bytes log2Align <? freeListCount
  then altFlClassBytes (freeSizeClass bytes log2Align) - bytes
  else 0.

Definition altFlBlockAlignment (bytes log2Align : Z) : Z :=
  if freeSizeClass bytes log2Align <? freeListCount
  then altFlClassBytes (freeSizeClass bytes log2Align)
  else 2 ^ log2Align.

Definition altFlBlockFacts (pointer bytes log2Align : Z) : Prop :=
  mapRamBase defaultMap <= pointer /\
  pointer + bytes + altFlBlockSlack bytes log2Align <= machineRamEnd defaultMap /\
  (altFlBlockAlignment bytes log2Align | pointer).

Definition altFlBlock `{!islaG Sigma} `{!threadG}
    (pointer bytes log2Align : Z) : iProp Sigma :=
  ((pointer + bytes) ↦ₘ? altFlBlockSlack bytes log2Align ∗
   ⌜bytes <> 0 -> altFlBlockFacts pointer bytes log2Align⌝)%I.

Lemma altFlBlock_unfold `{!islaG Sigma} `{!threadG} (pointer bytes log2Align : Z) :
  altFlBlock pointer bytes log2Align ⊣⊢
  ((pointer + bytes) ↦ₘ? altFlBlockSlack bytes log2Align ∗
   ⌜bytes <> 0 -> altFlBlockFacts pointer bytes log2Align⌝)%I.
Proof. reflexivity. Qed.
Global Opaque altFlBlock.

(* The bytes alloc hands out: the request on success, none on null. *)
Definition altFlAllocatedBytes (pointer bytes : Z) : Z :=
  if pointer =? 0 then 0 else bytes.

(* The function table alt_fl_alloc.vtable in .rodata and the Allocator
   object {ptr, vtable} that names it. Callers own both and return them
   unchanged, so every jalr target is a loaded word with a known value. *)
Definition altFlVtableBytes : list byte :=
  word64Bytes sym_alt_fl_alloc_alloc ++ word64Bytes sym_alt_fl_alloc_resize ++
  word64Bytes sym_alt_fl_alloc_remap ++ word64Bytes sym_alt_fl_alloc_free.

Definition altFlVtable `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes)%I.
Global Instance : LithiumUnfold (@altFlVtable) := I.
Global Typeclasses Opaque altFlVtable.

Definition altFlAllocatorBytes (context : Z) : list byte :=
  word64Bytes context ++ word64Bytes sym_alt_fl_alloc_vtable.

Definition altFlAllocatorObject `{!islaG Sigma} `{!threadG}
    (pointer context : Z) : iProp Sigma :=
  (pointer ↦ₘ∗ altFlAllocatorBytes context)%I.
Global Instance : LithiumUnfold (@altFlAllocatorObject) := I.
Global Typeclasses Opaque altFlAllocatorObject.

(* alloc(ctx, len, log2 alignment, ret_addr) -> ?[*]u8. *)
Definition altFlAllocDomain (bytes log2Align : Z) : Prop :=
  0 < bytes < altFlMaxRequestBytes /\ 0 <= log2Align <= altFlMaxLog2Alignment.

Definition altFlAllocCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap altFlCallStackBytes
    (fun argv sp RET =>
      ⌜altFlAllocDomain (bv_unsigned (argv !!! 1%nat))
        (bv_unsigned (argv !!! 2%nat))⌝ ∗
      altFlHeap ∗
      RET (fun rets =>
        altFlHeap ∗
        bv_unsigned (rets !!! 0%nat) ↦ₘ?
          altFlAllocatedBytes (bv_unsigned (rets !!! 0%nat))
            (bv_unsigned (argv !!! 1%nat)) ∗
        altFlBlock (bv_unsigned (rets !!! 0%nat))
          (altFlAllocatedBytes (bv_unsigned (rets !!! 0%nat))
            (bv_unsigned (argv !!! 1%nat)))
          (bv_unsigned (argv !!! 2%nat)) ∗
        True)))%I.
Global Instance : LithiumUnfold (@altFlAllocCallSpec) := I.
Global Typeclasses Opaque altFlAllocCallSpec.

(* remap(ctx, memory.ptr, memory.len, log2 alignment, new_len, ret_addr):
   alt_fl_alloc.remap returns null and touches no memory. *)
Definition altFlRemapCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap altFlCallStackBytes
    (fun argv sp RET =>
      RET (fun rets => ⌜bv_unsigned (rets !!! 0%nat) = 0⌝ ∗ True)))%I.
Global Instance : LithiumUnfold (@altFlRemapCallSpec) := I.
Global Typeclasses Opaque altFlRemapCallSpec.

(* free(ctx, memory.ptr, memory.len, log2 alignment, ret_addr). The caller
   gives up the block and its token. *)
Definition altFlFreeDomain (bytes log2Align : Z) : Prop :=
  0 < bytes < altFlMaxRequestBytes /\ 0 <= log2Align <= altFlMaxLog2Alignment.

Definition altFlFreeCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap altFlCallStackBytes
    (fun argv sp RET =>
      ⌜altFlFreeDomain (bv_unsigned (argv !!! 2%nat))
        (bv_unsigned (argv !!! 3%nat))⌝ ∗
      altFlHeap ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat) ∗
      altFlBlock (bv_unsigned (argv !!! 1%nat)) (bv_unsigned (argv !!! 2%nat))
        (bv_unsigned (argv !!! 3%nat)) ∗
      RET (fun _ => altFlHeap ∗ True)))%I.
Global Instance : LithiumUnfold (@altFlFreeCallSpec) := I.
Global Typeclasses Opaque altFlFreeCallSpec.

(* The trusted runtime premises: each allocator entry satisfies its spec. *)
Definition altFlAllocCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec)%I.
Global Instance : LithiumUnfold (@altFlAllocCallPremise) := I.
Global Typeclasses Opaque altFlAllocCallPremise.

Definition altFlRemapCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec)%I.
Global Instance : LithiumUnfold (@altFlRemapCallPremise) := I.
Global Typeclasses Opaque altFlRemapCallPremise.

Definition altFlFreeCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec)%I.
Global Instance : LithiumUnfold (@altFlFreeCallPremise) := I.
Global Typeclasses Opaque altFlFreeCallPremise.

Definition altFlAllocatorPremises `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (altFlAllocCallPremise ∗ altFlRemapCallPremise ∗ altFlFreeCallPremise)%I.
Global Instance : LithiumUnfold (@altFlAllocatorPremises) := I.
Global Typeclasses Opaque altFlAllocatorPremises.
