From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* StoreMemoryLookup.zesu_join_frame_explicit (decodeParentHeader 03bc): a
   request for one byte array spelled as an explicit list, where the block
   holds a cell at its address and the adjacent pieces that make up exactly
   the requested length (zero-size regions are skipped). *)
Notation z8 := (BV 8 0) (only parsing).
Notation zeros10 := [z8; z8; z8; z8; z8; z8; z8; z8; z8; z8] (only parsing).

Lemma test_frame_fold_explicit `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ? 0 -∗ (a + 8) ↦ₘ (BV 16 0) -∗ (a + 10) ↦ₘ? 6 -∗ K -∗
  (∃ y : unit, a ↦ₘ∗ zeros10 ∗ ⌜y = tt⌝) ∗ (a + 10) ↦ₘ? 6 ∗ K.
Proof.
  iStartProof. iIntros "H0 Hz H1 Ht HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit.
  iFrame. by iExists tt.
Qed.


Print Assumptions test_frame_fold_explicit.

(* Refused: a gap; a piece that goes past the requested length; bytes that
   are not the requested ones; an array held at the address. *)
Lemma test_frame_fold_explicit_gap `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  (a ↦ₘ∗ zeros10 ∗ K) -∗ a ↦ₘ (BV 64 0) -∗ (a + 9) ↦ₘ (BV 16 0) -∗ a ↦ₘ∗ zeros10 ∗ K.
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit).
  iExact "HG".
Qed.

Lemma test_frame_fold_explicit_overshoot `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  (a ↦ₘ∗ zeros10 ∗ K) -∗ a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ (BV 64 0) -∗ a ↦ₘ∗ zeros10 ∗ K.
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit).
  iExact "HG".
Qed.

Lemma test_frame_fold_explicit_other_bytes `{!islaG Sigma} (a : Z) (x : bv 64) (K : iProp Sigma) :
  (a ↦ₘ∗ zeros10 ∗ K) -∗ a ↦ₘ x -∗ (a + 8) ↦ₘ (BV 16 0) -∗ a ↦ₘ∗ zeros10 ∗ K.
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit).
  iExact "HG".
Qed.

Lemma test_frame_fold_explicit_array_held `{!islaG Sigma} (a : Z) (l : list (bv 8)) (K : iProp Sigma) :
  (a ↦ₘ∗ zeros10 ∗ K) -∗ a ↦ₘ∗ l -∗ a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ (BV 16 0) -∗ a ↦ₘ∗ zeros10 ∗ K.
Proof.
  iIntros "HG Hl H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit).
  iExact "HG".
Qed.

(* The cell at the requested address spelled on the same root at offset 0
   (decodeParentHeader 0514_slot2: request at `R + 8 + … + 8`, stored cell at
   `R + 64`): the cell is restated at the requested address and the fold
   proceeds. Refused: a cell on the same root at another offset. *)
Lemma test_frame_fold_explicit_offset_spelling `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  (a + 8) ↦ₘ (BV 64 0) -∗ (a + 16) ↦ₘ (BV 16 0) -∗ K -∗
  ((a + 4 + 4) ↦ₘ∗ zeros10 ∗ K).
Proof.
  iIntros "H0 H1 HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit.
  iFrame.
Qed.

Lemma test_frame_fold_explicit_offset_other `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  ((a + 4 + 4) ↦ₘ∗ zeros10 ∗ K) -∗
  (a + 9) ↦ₘ (BV 64 0) -∗ (a + 17) ↦ₘ (BV 16 0) -∗
  ((a + 4 + 4) ↦ₘ∗ zeros10 ∗ K).
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit).
  iExact "HG".
Qed.
