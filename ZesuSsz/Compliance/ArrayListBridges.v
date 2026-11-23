(* Bridges between the array-list contract boundary (ArrayListContract.v) and
   the generated block entries of the array-list regions (keysEnsureCapacity,
   keysToOwnedSlice, entriesToOwnedSlice): header bytes and their words, the
   buffer fold, the callee-saved registers, the allocator objects, and the
   byte-level frame steps of a prologue or epilogue. Nothing here names one
   region. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ArrayListContract.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- Words of byte lists. ---- *)

Lemma arrayList_word64Bytes_le (value : Z) :
  word64Bytes value = bv_to_little_endian 8 8 value.
Proof.
  rewrite zesu_word64_bytes_encoding. unfold word64Bytes. reflexivity.
Qed.

Lemma arrayList_word64Bytes_length (value : Z) : length (word64Bytes value) = 8%nat.
Proof. reflexivity. Qed.

Lemma arrayList_word64Bytes_word (value : Z) :
  0 <= value < 2 ^ 64 -> little_endian_to_bv 8 (word64Bytes value) = value.
Proof.
  intros Hv. rewrite arrayList_word64Bytes_le.
  rewrite little_endian_to_bv_to_little_endian; [|lia].
  apply Z.mod_small. cbn. lia.
Qed.

Lemma arrayList_take_drop_app (k : nat) (l1 l2 : list byte) :
  length l1 = k -> take 8 (drop k (l1 ++ l2)) = take 8 l2.
Proof. intros <-. rewrite drop_app_length. reflexivity. Qed.

Lemma arrayList_take8_word (value : Z) (rest : list byte) :
  take 8 (word64Bytes value ++ rest) = word64Bytes value.
Proof. reflexivity. Qed.

(* ---- The header: {items.ptr, items.len, capacity}. ---- *)

Lemma arrayListHeaderBytes_length (state : ArrayListState) :
  length (arrayListHeaderBytes state) = 24%nat.
Proof. reflexivity. Qed.

Lemma arrayListHeaderBytes_words (state : ArrayListState) :
  take 8 (drop 0 (arrayListHeaderBytes state)) = word64Bytes (arrayListPointer state) /\
  take 8 (drop 8 (arrayListHeaderBytes state)) = word64Bytes (arrayListLength state) /\
  take 8 (drop 16 (arrayListHeaderBytes state)) = word64Bytes (arrayListCapacity state).
Proof.
  unfold arrayListHeaderBytes. split_and!; reflexivity.
Qed.

(* The header word at byte OFFSET (0, 8, 16) read little-endian. *)
Lemma arrayListHeaderBytes_word_values (state : ArrayListState) :
  0 <= arrayListPointer state < 2 ^ 64 ->
  0 <= arrayListLength state < 2 ^ 64 ->
  0 <= arrayListCapacity state < 2 ^ 64 ->
  little_endian_to_bv 8 (take 8 (drop 0 (arrayListHeaderBytes state))) = arrayListPointer state /\
  little_endian_to_bv 8 (take 8 (drop 8 (arrayListHeaderBytes state))) = arrayListLength state /\
  little_endian_to_bv 8 (take 8 (drop 16 (arrayListHeaderBytes state))) = arrayListCapacity state.
Proof.
  intros Hp Hl Hc. destruct (arrayListHeaderBytes_words state) as (-> & -> & ->).
  rewrite !arrayList_word64Bytes_word; auto.
Qed.

(* A header whose pointer and capacity words were stored (the growth path):
   the bytes of the new state. *)
Lemma arrayListHeaderBytes_store (state : ArrayListState) (pointer capacity : Z) :
  take 0 (arrayListHeaderBytes state) ++ word64Bytes pointer ++
    take 8 (drop 8 (arrayListHeaderBytes state)) ++ word64Bytes capacity =
  arrayListHeaderBytes {| arrayListPointer := pointer;
                          arrayListLength := arrayListLength state;
                          arrayListCapacity := capacity;
                          arrayListItems := arrayListItems state |}.
Proof.
  destruct (arrayListHeaderBytes_words state) as (_ & -> & _). reflexivity.
Qed.

(* ---- Allocator objects and the function table. ---- *)

Lemma altFlAllocatorBytes_length (context : Z) :
  length (altFlAllocatorBytes context) = 16%nat.
Proof. reflexivity. Qed.

Lemma altFlAllocatorBytes_words (context : Z) :
  0 <= context < 2 ^ 64 ->
  little_endian_to_bv 8 (take 8 (drop 0 (altFlAllocatorBytes context))) = context /\
  little_endian_to_bv 8 (take 8 (drop 8 (altFlAllocatorBytes context))) = sym_alt_fl_alloc_vtable.
Proof.
  intros Hc. unfold altFlAllocatorBytes. split.
  - rewrite drop_0 arrayList_take8_word. by apply arrayList_word64Bytes_word.
  - rewrite (arrayList_take_drop_app 8); [|reflexivity].
    rewrite take_ge; [|reflexivity]. vm_compute. reflexivity.
Qed.

Lemma altFlVtableBytes_length : length altFlVtableBytes = 32%nat.
Proof. reflexivity. Qed.

Lemma altFlVtableBytes_words :
  little_endian_to_bv 8 (take 8 (drop 0 altFlVtableBytes)) = sym_alt_fl_alloc_alloc /\
  little_endian_to_bv 8 (take 8 (drop 8 altFlVtableBytes)) = sym_alt_fl_alloc_resize /\
  little_endian_to_bv 8 (take 8 (drop 16 altFlVtableBytes)) = sym_alt_fl_alloc_remap /\
  little_endian_to_bv 8 (take 8 (drop 24 altFlVtableBytes)) = sym_alt_fl_alloc_free.
Proof. vm_compute. split_and!; reflexivity. Qed.

Section Resources.
Context `{!islaG Sigma} `{!threadG}.

Lemma altFlAllocatorObject_unfold (pointer context : Z) :
  altFlAllocatorObject pointer context ⊣⊢ pointer ↦ₘ∗ altFlAllocatorBytes context.
Proof. by rewrite /altFlAllocatorObject. Qed.

Lemma altFlVtable_unfold : altFlVtable ⊣⊢ sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes.
Proof. by rewrite /altFlVtable. Qed.

(* ---- The buffer and the callee-saved registers. ---- *)

Lemma arrayListBuffer_unfold (elementBytes log2Align : Z) (state : ArrayListState) :
  arrayListBuffer elementBytes log2Align state ⊣⊢
  arrayListPointer state ↦ₘ∗ arrayListItems state ∗
  (arrayListPointer state + arrayListLength state * elementBytes) ↦ₘ?
    ((arrayListCapacity state - arrayListLength state) * elementBytes) ∗
  altFlBlock (arrayListPointer state) (arrayListCapacity state * elementBytes) log2Align.
Proof. by rewrite /arrayListBuffer. Qed.

Lemma arrayListSavedRegisters_unfold (saved : ArrayListCalleeSaved) :
  arrayListSavedRegisters saved ⊣⊢
  "x8" ↦ᵣ RVal_Bits (savedX8 saved) ∗ "x9" ↦ᵣ RVal_Bits (savedX9 saved) ∗
  "x18" ↦ᵣ RVal_Bits (savedX18 saved) ∗ "x19" ↦ᵣ RVal_Bits (savedX19 saved) ∗
  "x20" ↦ᵣ RVal_Bits (savedX20 saved) ∗ "x21" ↦ᵣ RVal_Bits (savedX21 saved) ∗
  "x22" ↦ᵣ RVal_Bits (savedX22 saved) ∗ "x23" ↦ᵣ RVal_Bits (savedX23 saved) ∗
  "x24" ↦ᵣ RVal_Bits (savedX24 saved) ∗ "x25" ↦ᵣ RVal_Bits (savedX25 saved) ∗
  "x26" ↦ᵣ RVal_Bits (savedX26 saved) ∗ "x27" ↦ᵣ RVal_Bits (savedX27 saved).
Proof. by rewrite /arrayListSavedRegisters. Qed.

(* ---- Byte-level frame steps. ---- *)

Lemma arrayList_uninit_split (a m n : Z) :
  0 <= m <= n -> a ↦ₘ? n -∗ a ↦ₘ? m ∗ (a + m) ↦ₘ? (n - m).
Proof. iIntros (Hm) "H". by iApply (mem_mapsto_uninit_split m with "H"). Qed.

Lemma arrayList_uninit_join (a m n : Z) :
  0 <= m -> 0 <= n -> a ↦ₘ? m -∗ (a + m) ↦ₘ? n -∗ a ↦ₘ? (m + n).
Proof.
  iIntros (Hm Hn) "H1 H2".
  iApply (mem_mapsto_uninit_combine m a _ (m + n) with "H1 [H2]"); [lia|].
  by replace (m + n - m) with n by lia.
Qed.

Lemma arrayList_uninit_word (a : Z) : a ↦ₘ? 8 -∗ ∃ w : bv 64, a ↦ₘ w.
Proof.
  iIntros "H". iDestruct (mem_mapsto_uninit_to_mapsto with "H") as (n' b ->) "H".
  iExists b. iExact "H".
Qed.

Lemma arrayList_word_uninit (a : Z) (w : bv 64) : a ↦ₘ w -∗ a ↦ₘ? 8.
Proof. iIntros "H". iApply (mem_mapsto_mapsto_to_uninit with "H"). Qed.

Lemma arrayList_bytes_uninit (a : Z) (l : list (bv 8)) :
  a ↦ₘ∗ l -∗ a ↦ₘ? (Z.of_nat (length l)).
Proof.
  rewrite mem_mapsto_array_eq mem_mapsto_uninit_eq.
  iIntros "(%len & %Hlen & %Hrange & Hl)".
  assert (len = 1%N) as -> by lia.
  iExists (length l). iSplit; [done|]. iSplit; [iPureIntro; lia|].
  iApply (big_sepL_impl' with "Hl"); [by rewrite length_replicate|].
  iIntros "!>" (k v u Hv Hu) "Hv".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hv") as "Hu".
  rewrite mem_mapsto_uninit_eq.
  iDestruct "Hu" as (nn Hnn Hr) "Hb".
  assert (nn = 1%nat) as -> by (cbn in Hnn; lia).
  iDestruct "Hb" as "[[%b Hb] _]". iExists b.
  replace (a + k * Z.of_N 1 + 0%nat) with (a + k) by lia. done.
Qed.

End Resources.

(* ---- Ranges of a well-formed list. ---- *)

(* A list with capacity fits RAM, so its capacity is at most 2^24 elements of
   32 bytes (2^29 RAM bytes); a list without capacity has length 0. *)
Lemma arrayListWellFormed_capacity_bound (elementBytes : Z) (state : ArrayListState) :
  0 < elementBytes ->
  arrayListWellFormed elementBytes state ->
  arrayListCapacity state * elementBytes <= mapRamSize defaultMap.
Proof.
  intros He (Hl & _ & _ & Hram).
  destruct (Z.eq_dec (arrayListCapacity state) 0) as [->|Hc]; [cbn; lia|].
  destruct Hram as [Hlo Hhi]; [lia|].
  unfold machineRamEnd in Hhi. lia.
Qed.
