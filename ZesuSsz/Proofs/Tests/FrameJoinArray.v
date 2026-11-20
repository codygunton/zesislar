Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The successor asks for one byte array where the block holds a word cell,
   an uninitialised piece and a byte array, adjacent: they are presented as
   one array with its length. *)
Lemma frame_join_array `{!islaG Sigma} (a : Z) (v : bv 64) (bytes : list (bv 8)) :
  length bytes = 4%nat ->
  a ↦ₘ v -∗ (a + 8) ↦ₘ? 8 -∗ (a + 16) ↦ₘ∗ bytes -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ ⌜length l = 20%nat⌝.
Proof.
  intros Hbytes. iIntros "Hv Hu Hb".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  iExists _. iFrame. iPureIntro. lia.
Qed.

(* A piece that is not adjacent stays out of the run. *)
Lemma frame_join_array_gap `{!islaG Sigma} (a : Z) (v : bv 64) :
  a ↦ₘ v -∗ (a + 16) ↦ₘ? 8 -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ ⌜length l = 8%nat⌝ ∗ (a + 16) ↦ₘ? 8.
Proof.
  iIntros "Hv Hu".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  iExists _. iFrame. iPureIntro. lia.
Qed.

(* An array is already owned at the address: the step refuses. *)
Lemma frame_join_array_refuses_owned `{!islaG Sigma} (a : Z) (v : bv 64) (bytes : list (bv 8)) :
  a ↦ₘ∗ bytes -∗ a ↦ₘ v -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ True.
Proof.
  iIntros "Hb Hv".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  iExists _. iFrame.
Qed.

(* No cell at the address: the step refuses. *)
Lemma frame_join_array_refuses_no_cell `{!islaG Sigma} (a : Z) (v : bv 64) :
  a ↦ₘ? 8 -∗ (a + 8) ↦ₘ v -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ True.
Proof.
  iIntros "Hu Hv".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  iDestruct (ZesuSsz.Contracts.IslarisMemory.mem_mapsto_uninit_to_byte_array with "Hu")
    as (l) "[_ Hl]".
  iExists l. iFrame.
Qed.

(* The byte cells from index zero are held as one group `c0 ∗ c1 ∗ emp`: the
   group is opened and the cells are presented as the requested array. *)
Lemma frame_join_array_grouped `{!islaG Sigma} (a : Z) (b0 b1 : bv 8) :
  ((a + Z.of_nat 0 * 1) ↦ₘ b0 ∗ (a + Z.of_nat 1 * 1) ↦ₘ b1 ∗ emp) -∗
  ∃ x : bv 8, a ↦ₘ∗ [x; b1] ∗ ⌜x = b0⌝.
Proof.
  iIntros "Hcells".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  iExists b0. iFrame. done.
Qed.

(* A group whose base is not requested stays closed: the step refuses. *)
Lemma frame_join_array_grouped_refuses_other `{!islaG Sigma} (a : Z) (b0 b1 : bv 8) :
  ((a + Z.of_nat 0 * 1) ↦ₘ b0 ∗ (a + Z.of_nat 1 * 1) ↦ₘ b1 ∗ emp) -∗
  (a + 8) ↦ₘ∗ [b1] -∗
  ∃ x : bv 8, (a + 8) ↦ₘ∗ [x] ∗ True.
Proof.
  iIntros "Hcells Hb".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  idtac "GROUP_OTHER_REFUSAL_EXECUTED".
  iExists b1. iFrame.
Qed.

(* A word cell asked for as the explicit list of its byte extracts: the cell
   is that byte array and the witness is the stored word. *)
Lemma frame_join_word_cell_extracts `{!islaG Sigma} (a : Z) (w : bv 64) :
  ⊢ subsume (a ↦ₘ w) (λ x : bv 64, a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x; bv_extract 16 8 x; bv_extract 24 8 x; bv_extract 32 8 x; bv_extract 40 8 x; bv_extract 48 8 x; bv_extract 56 8 x]) (λ x, ⌜x = w⌝).
Proof.
  iStartProof.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  iExists w. iFrame. done.
Qed.

(* The shape of a stored word at a successor (decodeParentHeader 0348): the
   extracts are of a sum over the existential's component, and the run names
   the environment by a local definition. *)
Lemma frame_join_word_cell_extracts_alias `{!islaG Sigma} (a : Z) (w c : bv 64) :
  ⊢ subsume (a ↦ₘ (w + c)%bv)
      (λ x : bv 64 *ₗ (), a ↦ₘ∗ [bv_extract 0 8 (x.1ₗ + c); bv_extract 8 8 (x.1ₗ + c);
        bv_extract 16 8 (x.1ₗ + c); bv_extract 24 8 (x.1ₗ + c); bv_extract 32 8 (x.1ₗ + c);
        bv_extract 40 8 (x.1ₗ + c); bv_extract 48 8 (x.1ₗ + c); bv_extract 56 8 (x.1ₗ + c)])
      (λ x, ⌜x.1ₗ = w⌝).
Proof.
  iStartProof.
  lazymatch goal with |- environments.envs_entails ?context ?goal =>
    pose (frameContext := context); change (environments.envs_entails frameContext goal)
  end.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  iExists (w, tt)ₗ. iFrame. done.
Qed.

(* The array asked for is not the word's byte extracts: the step refuses. *)
Lemma frame_join_word_cell_refuses_other `{!islaG Sigma} (a : Z) (w : bv 64) (l : list (bv 8)) :
  a ↦ₘ∗ l -∗ subsume (a ↦ₘ w) (λ _ : unit, a ↦ₘ∗ l) (λ _, a ↦ₘ w).
Proof.
  iIntros "Hl".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_byte_array.
  idtac "WORD_CELL_OTHER_REFUSAL_EXECUTED".
  iIntros "Hw". iExists tt. iFrame.
Qed.

Print Assumptions frame_join_array.
Print Assumptions frame_join_array_gap.
Print Assumptions frame_join_array_refuses_owned.
Print Assumptions frame_join_array_refuses_no_cell.
Print Assumptions frame_join_array_grouped.
Print Assumptions frame_join_array_grouped_refuses_other.
Print Assumptions frame_join_word_cell_extracts.
Print Assumptions frame_join_word_cell_extracts_alias.
Print Assumptions frame_join_word_cell_refuses_other.
