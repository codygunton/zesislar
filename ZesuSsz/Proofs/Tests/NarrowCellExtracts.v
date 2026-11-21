From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* StoreMemoryLookup.zesu_subsume_narrow_cell_extracts: a cell narrower than a
   word (decodeParentHeader 0270: a 16-bit tag stored from x10) asked for as
   the explicit list of its byte extracts is that byte array. *)

(* Fires: the existential on the left of a separating conjunction, sealed and
   opened; no existential; a subsumption; a 24-bit cell. *)
Lemma test_narrow_cell_exist_sep `{!islaG Sigma} (a : Z) (x : bv 64) (K : iProp Sigma) :
  a ↦ₘ bv_extract 0 16 x -∗ K -∗
  (∃ y : unit, a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x] ∗ ⌜y = tt⌝) ∗ K.
Proof.
  iStartProof. iIntros "H HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts.
  iFrame "HK". by iExists tt.
Qed.

Lemma test_narrow_cell_exist_opened `{!islaG Sigma} (a : Z) (x : bv 64) :
  a ↦ₘ bv_extract 0 16 x -∗
  ∃ y : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1)
    [bv_extract 0 8 x; bv_extract 8 8 x] ∗ ⌜y = tt⌝.
Proof.
  iStartProof. iIntros "H".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts.
  by iExists tt.
Qed.

Lemma test_narrow_cell_sep `{!islaG Sigma} (a : Z) (x : bv 64) (K : iProp Sigma) :
  a ↦ₘ bv_extract 0 16 x -∗ K -∗ a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x] ∗ K.
Proof.
  iStartProof. iIntros "H HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts.
  iFrame "HK".
Qed.

Lemma test_narrow_cell_subsume `{!islaG Sigma} (a : Z) (x : bv 64) (T : unit → iProp Sigma) :
  (∃ y, T y) ⊢
  subsume (a ↦ₘ bv_extract 0 16 x) (λ _, a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x]) T.
Proof.
  iStartProof. iIntros "[%y HT]".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts.
  iExists y. iFrame.
Qed.

Lemma test_narrow_cell_24 `{!islaG Sigma} (a : Z) (x : bv 64) (K : iProp Sigma) :
  a ↦ₘ bv_extract 0 24 x -∗ K -∗
  a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x; bv_extract 16 8 x] ∗ K.
Proof.
  iStartProof. iIntros "H HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts.
  iFrame "HK".
Qed.

Print Assumptions test_narrow_cell_exist_sep.
Print Assumptions test_narrow_cell_subsume.

(* Refused: the extracts of another register; a cell at another address; a
   byte cell; a request one byte short; a 64-bit cell (the word rule's), even
   when its eight extracts are asked. *)
Lemma test_narrow_cell_refused `{!islaG Sigma} (a : Z) (x y : bv 64) (K : iProp Sigma) : True.
Proof.
  Fail assert (⊢ a ↦ₘ bv_extract 0 16 x -∗ K -∗
    (∃ u : unit, a ↦ₘ∗ [bv_extract 0 8 y; bv_extract 8 8 y] ∗ ⌜u = tt⌝) ∗ K) by
    (iStartProof; iIntros "H HK";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts).
  Fail assert (⊢ (a + 2) ↦ₘ bv_extract 0 16 x -∗ K -∗
    (∃ u : unit, a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x] ∗ ⌜u = tt⌝) ∗ K) by
    (iStartProof; iIntros "H HK";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts).
  Fail assert (⊢ a ↦ₘ (bv_extract 0 8 x : bv 8) -∗ K -∗
    (∃ u : unit, a ↦ₘ∗ [bv_extract 0 8 x] ∗ ⌜u = tt⌝) ∗ K) by
    (iStartProof; iIntros "H HK";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts).
  Fail assert (⊢ a ↦ₘ bv_extract 0 24 x -∗ K -∗
    a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x] ∗ K) by
    (iStartProof; iIntros "H HK";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts).
  Fail assert (⊢ a ↦ₘ x -∗ K -∗
    a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x; bv_extract 16 8 x; bv_extract 24 8 x;
           bv_extract 32 8 x; bv_extract 40 8 x; bv_extract 48 8 x; bv_extract 56 8 x] ∗ K) by
    (iStartProof; iIntros "H HK";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts).
  exact I.
Qed.

(* The word rule keeps main's subsumption form: a 64-bit cell against the
   extracts of the existential's witness (the request mentions the bound
   variable). The width-generic rewrite of 316f6fe95 matched only requests
   closed in the witness and lost this shape (decodeParentHeader 0498: the
   frame join succeeds twice on main, never with that rewrite). *)
Lemma test_word_cell_subsume_witness_extracts `{!islaG Sigma} (a : Z) (w : bv 64)
    (T : bv 64 → iProp Sigma) :
  T w ⊢
  subsume (a ↦ₘ w) (λ v, a ↦ₘ∗ [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v;
    bv_extract 24 8 v; bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v;
    bv_extract 56 8 v]) T.
Proof.
  iStartProof. iIntros "HT".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iExists w. iFrame.
Qed.

(* ... and the narrow rule does not take that shape. *)
Lemma test_word_cell_subsume_witness_not_narrow `{!islaG Sigma} (a : Z) (w : bv 64)
    (T : bv 64 → iProp Sigma) : True.
Proof.
  Fail assert (T w ⊢
    subsume (a ↦ₘ w) (λ v, a ↦ₘ∗ [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v;
      bv_extract 24 8 v; bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v;
      bv_extract 56 8 v]) T) by
    (iStartProof; iIntros "HT";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_narrow_cell_extracts).
  exact I.
Qed.

Print Assumptions test_word_cell_subsume_witness_extracts.
