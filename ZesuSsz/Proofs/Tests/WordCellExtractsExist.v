From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* decodeParentHeader 04b0/0570/05a4: a successor asks, as the first resource
   under its existential, for the byte extracts of a word spelled as
   `bv_concat` of the bytes `nth k bytes`, where the block holds the word cell
   with the value as loaded, `Z_to_bv 64 (little_endian_to_bv 8 (take 8
   (drop 0 bytes)))`. The cell is presented as those extracts once the two
   spellings are shown equal (StoreMemoryLookup.zesu_subsume_word_cell_extracts,
   existential heads). *)
Definition test_concat_word (bytes : list (bv 8)) : bv 64 :=
  bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (nth 7 bytes 0%bv) (nth 6 bytes 0%bv)) (nth 5 bytes 0%bv))
    (nth 4 bytes 0%bv)) (nth 3 bytes 0%bv)) (nth 2 bytes 0%bv)) (nth 1 bytes 0%bv))
    (nth 0 bytes 0%bv).
Notation extracts v :=
  [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v; bv_extract 24 8 v;
   bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v; bv_extract 56 8 v].

(* Sealed array under the existential head. *)
Lemma test_word_cell_extracts_exist `{!islaG Sigma} (a : Z) (bytes : list (bv 8)) :
  length bytes = 16%nat ->
  a ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗
  ∃ x : unit, a ↦ₘ∗ extracts (test_concat_word bytes) ∗ ⌜x = tt⌝.
Proof.
  intros Hlen. iStartProof. iIntros "H". unfold test_concat_word.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  by iExists tt.
Qed.

(* Opened array (`mem_mapsto_array_def`) under the existential head. *)
Lemma test_word_cell_extracts_exist_opened `{!islaG Sigma} (a : Z) (bytes : list (bv 8)) :
  length bytes = 16%nat ->
  a ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗
  ∃ x : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1)
    (extracts (test_concat_word bytes)) ∗ ⌜x = tt⌝.
Proof.
  intros Hlen. iStartProof. iIntros "H". unfold test_concat_word.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  by iExists tt.
Qed.

(* 05a4: the existential is the left part of a separating conjunction (the
   successor's pure tail and continuation follow it). *)
Lemma test_word_cell_extracts_exist_sep `{!islaG Sigma} (a : Z) (bytes : list (bv 8)) (K : iProp Sigma) :
  length bytes = 16%nat ->
  a ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗ K -∗
  (∃ x : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1)
    (extracts (test_concat_word bytes)) ∗ ⌜x = tt⌝) ∗ K.
Proof.
  intros Hlen. iStartProof. iIntros "H HK". unfold test_concat_word.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iFrame "HK". by iExists tt.
Qed.

(* 04b0/0570: no existential, the cells are the first resource of the request. *)
Lemma test_word_cell_extracts_sep `{!islaG Sigma} (a : Z) (bytes : list (bv 8)) (K : iProp Sigma) :
  length bytes = 16%nat ->
  a ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗ K -∗
  isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) (extracts (test_concat_word bytes)) ∗ K.
Proof.
  intros Hlen. iStartProof. iIntros "H HK". unfold test_concat_word.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iFrame "HK".
Qed.

(* 05a4 at cc62c0252: the request goes on past the word, `a ↦ₘ∗ (extracts
   ++ [b])` (the word and the byte stored after it as one 9-byte array). The
   cell gives the eight extracts; `(a + 8) ↦ₘ∗ [b]` stays asked in their
   place. Under the existential on the left of a separating conjunction, and
   with no existential. *)
Notation extracts_then v b :=
  [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v; bv_extract 24 8 v;
   bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v; bv_extract 56 8 v; b].

Lemma test_word_cell_extracts_rest_exist_sep `{!islaG Sigma} (a : Z) (bytes : list (bv 8))
    (b : bv 8) (K : iProp Sigma) :
  length bytes = 16%nat ->
  a ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗
  (a + 8) ↦ₘ∗ [b] -∗ K -∗
  (∃ x : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1)
    (extracts_then (test_concat_word bytes) b) ∗ ⌜x = tt⌝) ∗ K.
Proof.
  intros Hlen. iStartProof. iIntros "H Hb HK". unfold test_concat_word.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iFrame "HK". iExists tt. by iFrame "Hb".
Qed.

Lemma test_word_cell_extracts_rest_sep `{!islaG Sigma} (a : Z) (bytes : list (bv 8))
    (b : bv 8) (K : iProp Sigma) :
  length bytes = 16%nat ->
  a ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗
  (a + 8) ↦ₘ∗ [b] -∗ K -∗
  isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) (extracts_then (test_concat_word bytes) b) ∗ K.
Proof.
  intros Hlen. iStartProof. iIntros "H Hb HK". unfold test_concat_word.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iFrame "HK Hb".
Qed.

(* Refused in that shape: a cell at another address. *)
Lemma test_word_cell_extracts_exist_sep_refused `{!islaG Sigma} (a : Z) (bytes : list (bv 8)) (K : iProp Sigma) :
  True.
Proof.
  Fail assert (⊢ (a + 8) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗ K -∗
    (∃ x : unit, a ↦ₘ∗ extracts (test_concat_word bytes) ∗ ⌜x = tt⌝) ∗ K) by
    (iStartProof; iIntros "H HK"; unfold test_concat_word;
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts).
  exact I.
Qed.

Print Assumptions test_word_cell_extracts_exist.
Print Assumptions test_word_cell_extracts_exist_opened.

(* Refused: the bytes of another list (the two spellings are not shown
   equal), and a cell at another address. *)
Lemma test_word_cell_extracts_exist_refused `{!islaG Sigma} (a : Z) (bytes other : list (bv 8)) :
  length bytes = 16%nat -> True.
Proof.
  intros Hlen.
  Fail assert (⊢ a ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗
    ∃ x : unit, a ↦ₘ∗ extracts (test_concat_word other) ∗ ⌜x = tt⌝) by
    (iStartProof; iIntros "H"; unfold test_concat_word;
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts).
  Fail assert (⊢ (a + 8) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop 0 bytes))) -∗
    ∃ x : unit, a ↦ₘ∗ extracts (test_concat_word bytes) ∗ ⌜x = tt⌝) by
    (iStartProof; iIntros "H"; unfold test_concat_word;
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts).
  exact I.
Qed.

(* Width-generic (decodeParentHeader 0270, 03bc): a 16-bit cell cut from a
   register asked as the register's two low extracts, sealed and opened; a
   zero word asked as zero bytes followed by more bytes, in a request and as a
   subsumption. *)
Lemma test_half_cell_extracts `{!islaG Sigma} (a : Z) (x : bv 64) (K : iProp Sigma) :
  a ↦ₘ bv_extract 0 16 x -∗ K -∗
  (∃ y : unit, a ↦ₘ∗ [bv_extract 0 8 x; bv_extract 8 8 x] ∗ ⌜y = tt⌝) ∗ K.
Proof.
  iStartProof. iIntros "H HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iFrame "HK". by iExists tt.
Qed.

Lemma test_half_cell_extracts_opened `{!islaG Sigma} (a : Z) (x : bv 64) (K : iProp Sigma) :
  a ↦ₘ bv_extract 0 16 x -∗ K -∗
  (∃ y : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1)
    [bv_extract 0 8 x; bv_extract 8 8 x] ∗ ⌜y = tt⌝) ∗ K.
Proof.
  iStartProof. iIntros "H HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iFrame "HK". by iExists tt.
Qed.

Lemma test_zero_word_cell_rest `{!islaG Sigma} (a : Z) (z : bv 8) (K : iProp Sigma) :
  a ↦ₘ (0 : bv 64) -∗ (a + 8) ↦ₘ∗ [z; z] -∗ K -∗
  a ↦ₘ∗ [0%bv; 0%bv; 0%bv; 0%bv; 0%bv; 0%bv; 0%bv; 0%bv; z; z] ∗ K.
Proof.
  iStartProof. iIntros "H Hz HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iFrame "HK Hz".
Qed.

Lemma test_zero_word_cell_subsume_rest `{!islaG Sigma} (a : Z) (z : bv 8) (T : unit → iProp Sigma) :
  (∃ y, (a + 8) ↦ₘ∗ [z] ∗ T y) ⊢
  subsume (a ↦ₘ (0 : bv 64)) (λ _, a ↦ₘ∗ [0%bv; 0%bv; 0%bv; 0%bv; 0%bv; 0%bv; 0%bv; 0%bv; z]) T.
Proof.
  iStartProof. iIntros "H".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts.
  iExact "H".
Qed.

(* Refused: the extracts of another register; a byte cell (one byte is not
   this rule's shape). *)
Lemma test_half_cell_extracts_refused `{!islaG Sigma} (a : Z) (x y : bv 64) (K : iProp Sigma) : True.
Proof.
  Fail assert (⊢ a ↦ₘ bv_extract 0 16 x -∗ K -∗
    (∃ u : unit, a ↦ₘ∗ [bv_extract 0 8 y; bv_extract 8 8 y] ∗ ⌜u = tt⌝) ∗ K) by
    (iStartProof; iIntros "H HK";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts).
  Fail assert (⊢ a ↦ₘ (bv_extract 0 8 x : bv 8) -∗ K -∗
    (∃ u : unit, a ↦ₘ∗ [bv_extract 0 8 x] ∗ ⌜u = tt⌝) ∗ K) by
    (iStartProof; iIntros "H HK";
     ZesuSsz.Automation2.StoreMemoryLookup.zesu_subsume_word_cell_extracts).
  exact I.
Qed.

Print Assumptions test_half_cell_extracts.
Print Assumptions test_zero_word_cell_subsume_rest.

(* A word rebuilt from its own extracts (WrappedWord.zesu_word_extracts_rewrite,
   run by the finisher's list closer). *)
Lemma test_word_extracts_roundtrip (w : bv 64) :
  extracts w = extracts (Z_to_bv 64 (little_endian_to_bv 8 (extracts w))).
Proof. ZesuSsz.Automation2.Finish.zesu_finish_known_list_shape. Qed.

Print Assumptions test_word_extracts_roundtrip.

(* Refused: extracts out of order are not the word. *)
Lemma test_word_extracts_roundtrip_refused (w : bv 64) : True.
Proof.
  Fail assert (Z_to_bv 64 (little_endian_to_bv 8
    [bv_extract 8 8 w; bv_extract 0 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
     bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w]) = w)
    by ZesuSsz.Automation2.WrappedWord.zesu_word_extracts_rewrite.
  exact I.
Qed.
