Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Lemma fold_nested_control `{!islaG Sigma} (base : Z) (q : dfrac)
 (cells : list (bv 8)) (prefix suffix : iProp Sigma) :
 (0 <= base + 3 /\ base + 3 + Z.of_nat (length cells) <= 2^64) ->
 (prefix ∗ ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + Z.of_nat (3+i)) q v) ∗ suffix) -∗
 (prefix ∗ mem_mapsto_array (base + 3) q cells ∗ suffix).
Proof.
 intros Hbound. iIntros "Howners".
 ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
 iExact "Howners".
Qed.
Lemma refuse_word_cells `{!islaG Sigma} (base : Z) (q : dfrac) (cells : list (bv 64)) :
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + Z.of_nat (3+i)) q v) -∗
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + Z.of_nat (3+i)) q v).
Proof.
 iIntros "Hcells". assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
 idtac "WORD_OWNER_REFUSAL_EXECUTED". iAssumption.
Qed.
Lemma refuse_nonaffine_cells `{!islaG Sigma} (base : Z) (q : dfrac) (cells : list (bv 8)) :
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + 2 * Z.of_nat i) q v) -∗
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + 2 * Z.of_nat i) q v).
Proof.
 iIntros "Hcells". assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
 idtac "NONAFFINE_OWNER_REFUSAL_EXECUTED". iAssumption.
Qed.
Print Assumptions fold_nested_control.
Print Assumptions refuse_word_cells.
Print Assumptions refuse_nonaffine_cells.

Lemma fold_stride_and_length `{!islaG Sigma} (base : Z) (stride : N)
    (values : list (bv 8)) :
  (8 = stride * 8)%N -> length values = 7%nat ->
  (0 <= base + 3 /\ base + 3 + Z.of_nat (length (skipn 3 values)) <= 2^64) ->
  ([∗ list] i ↦ v ∈ skipn 3 values,
    mem_mapsto (base + Z.of_nat (3+i) * Z.of_N stride) (DfracOwn 1) v) -∗
  mem_mapsto_array (base + 3) (DfracOwn 1) (skipn 3 values).
Proof.
  intros Hwidth Hsource Hbound. iIntros "Hcells".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
  match goal with Hlength : length (skipn 3 values) = ?count |- _ =>
    assert (count = 4%nat) by reflexivity
  end.
  iAssumption.
Qed.

Lemma retain_real_fold_progress `{!islaG Sigma} (base probe : Z)
    (cells : list (bv 8)) (prefix suffix : iProp Sigma) :
  (0 <= base + 3 /\ base + 3 + Z.of_nat (length cells) <= 2^64) ->
  (prefix ∗ ([∗ list] i ↦ v ∈ cells,
    mem_mapsto (base + Z.of_nat (3+i)) (DfracOwn 1) v) ∗ suffix) -∗
  find_in_context (FindMemMapsTo probe) (fun _ => prefix ∗ suffix)%I.
Proof.
  intro Hbound. iIntros "Howners".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
  rewrite /find_in_context /FindMemMapsTo.
  iExists (MKArray 8 (base + 3) cells).
  cbn [fic_Prop mem_mapsto_kind_prop]. iFrame.
Qed.

Lemma refusal_preserves_stride `{!islaG Sigma} (base : Z) (stride : N)
    (cells : list (bv 8)) :
  (8 = stride * 8)%N ->
  ([∗ list] i ↦ v ∈ cells,
    mem_mapsto (base + 2 * Z.of_nat i * Z.of_N stride) (DfracOwn 1) v) -∗
  ([∗ list] i ↦ v ∈ cells,
    mem_mapsto (base + 2 * Z.of_nat i * Z.of_N stride) (DfracOwn 1) v).
Proof.
  intro Hwidth. iIntros "Hcells".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
  is_var stride. iAssumption.
Qed.

Lemma selected_store_mod (base : Z) :
  0 <= base /\ base + 3 < 2^64 ->
  SHELVED_SIDECOND
    ((bv_unsigned (bv_add (Z_to_bv 64 base) (BV 64 3)) - (base + 3)) mod 1 = 0).
Proof.
  intro Hbound. ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_splice_bounds.
Qed.

Lemma selected_store_nonnegative (base : Z) :
  0 <= base /\ base + 3 < 2^64 ->
  SHELVED_SIDECOND
    (0 <= (bv_unsigned (bv_add (Z_to_bv 64 base) (BV 64 3)) - (base + 3)) / 1).
Proof.
  intro Hbound. ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_splice_bounds.
Qed.

Lemma selected_store_index (base : Z) (cells : list (bv 8)) :
  0 <= base /\ base + 3 < 2^64 -> length cells = 4%nat ->
  SHELVED_SIDECOND
    ((Z.to_nat ((bv_unsigned (bv_add (Z_to_bv 64 base) (BV 64 3)) - (base + 3)) / 1)
      < length cells)%nat).
Proof.
  intros Hbound Hlength. ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_splice_bounds.
Qed.

Lemma selected_store_rejects_unrelated_length (base : Z)
    (cells other : list (bv 8)) :
  0 <= base /\ base + 3 < 2^64 -> length other = 4%nat -> True.
Proof.
  intros Hbound Hother.
  assert_fails
    (assert (SHELVED_SIDECOND
      ((Z.to_nat ((bv_unsigned (bv_add (Z_to_bv 64 base) (BV 64 3)) - (base + 3)) / 1)
        < length cells)%nat)) by
      ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_splice_bounds).
  exact I.
Qed.

Print Assumptions fold_stride_and_length.
Print Assumptions retain_real_fold_progress.
Print Assumptions refusal_preserves_stride.
Print Assumptions selected_store_mod.
Print Assumptions selected_store_nonnegative.
Print Assumptions selected_store_index.
Print Assumptions selected_store_rejects_unrelated_length.
