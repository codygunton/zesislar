From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* StoreMemoryLookup.zesu_join_frame_explicit_exist (decodeParentHeader 0514
   return slots): the successor asks for one byte array spelled as an explicit
   list whose padding bytes are its own existential; the block holds a word
   cell, a word stored with a flag byte, a 16-bit cell and an uninitialised
   region that make up exactly the requested length. The existential bytes
   are instantiated with the held bytes at their positions. *)
Notation z8 := (BV 8 0) (only parsing).
Notation P2 := (bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ unit) (only parsing).

Lemma test_frame_fold_existential `{!islaG Sigma} (a : Z) (w : bv 64) (values : list (bv 8))
    (K : iProp Sigma) :
  a ↦ₘ w -∗ (a + 8) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 (1%bv :: take 7 values))) -∗ (a + 16) ↦ₘ (BV 16 0) -∗ (a + 18) ↦ₘ? 2 -∗ K -∗
  (∃ x : P2,
     a ↦ₘ∗ [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
            bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w;
            1%bv; x.1ₗ; x.2ₗ; x.3ₗ; x.4ₗ; x.5ₗ; x.6ₗ; bv_extract (56 - 8 - 8 - 8 - 8 - 8 - 8 - 8) 8 x.7ₗ;
            z8; z8; x.8ₗ; x.9ₗ] ∗
     ⌜x.1ₗ = bv_extract 8 8 (Z_to_bv 64 (little_endian_to_bv 8 (1%bv :: take 7 values))) /\ x.7ₗ = bv_extract 56 8 (Z_to_bv 64 (little_endian_to_bv 8 (1%bv :: take 7 values)))⌝ ∗ K).
Proof.
  iStartProof. iIntros "H0 H1 H2 H3 HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist.
  cbv [li_fst li_snd]. iFrame. iPureIntro. split; reflexivity.
Qed.

Print Assumptions test_frame_fold_existential.

(* The same fold where the request spells the flag word as a concatenation
   of its existential bytes over the flag `1` (decodeParentHeader 0514_slot3:
   the successor's word `bv_concat 64 (… x.7 … x.1) 1`, asked as its byte
   extracts). Each requested byte `bv_extract k 8 (bv_concat …)` is reduced by
   `zesu_byte_concat_low/high` to the concatenated byte, which is then the
   held byte. Without the concat tier the fold refuses (its byte check fails)
   and this proof does not go through. *)
Local Notation FW values := (Z_to_bv 64 (little_endian_to_bv 8 (1%bv :: take 7 values))) (only parsing).
Local Notation CW x := (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32
    (bv_concat 24 (bv_concat 16 x.7ₗ x.6ₗ) x.5ₗ) x.4ₗ) x.3ₗ) x.2ₗ) x.1ₗ) (BV 8 1)) (only parsing).
Lemma test_frame_fold_existential_concat_word `{!islaG Sigma} (a : Z) (w : bv 64)
    (values : list (bv 8)) (K : iProp Sigma) :
  a ↦ₘ w -∗ (a + 8) ↦ₘ FW values -∗ (a + 16) ↦ₘ (BV 16 0) -∗ (a + 18) ↦ₘ? 2 -∗ K -∗
  (∃ x : P2,
     a ↦ₘ∗ [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
            bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w;
            bv_extract 0 8 (CW x); bv_extract 8 8 (CW x); bv_extract 16 8 (CW x);
            bv_extract 24 8 (CW x); bv_extract 32 8 (CW x); bv_extract 40 8 (CW x);
            bv_extract 48 8 (CW x); bv_extract 56 8 (CW x);
            z8; z8; x.8ₗ; x.9ₗ] ∗
     ⌜x.1ₗ = bv_extract 8 8 (FW values) /\ x.7ₗ = bv_extract 56 8 (FW values)⌝ ∗ K).
Proof.
  iStartProof. iIntros "H0 H1 H2 H3 HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist.
  cbv [li_fst li_snd]. iFrame. iPureIntro. split; reflexivity.
Qed.
Print Assumptions test_frame_fold_existential_concat_word.

(* Refused through the concat tier: the concatenated flag byte is 2, the held
   flag byte is 1. *)
Local Notation CW2 x := (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32
    (bv_concat 24 (bv_concat 16 x.7ₗ x.6ₗ) x.5ₗ) x.4ₗ) x.3ₗ) x.2ₗ) x.1ₗ) (BV 8 2)) (only parsing).
Lemma test_frame_fold_existential_concat_other_flag `{!islaG Sigma} (a : Z) (w : bv 64)
    (values : list (bv 8)) (K : iProp Sigma) :
  (∃ x : P2, a ↦ₘ∗ [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
            bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w;
            bv_extract 0 8 (CW2 x); bv_extract 8 8 (CW2 x); bv_extract 16 8 (CW2 x);
            bv_extract 24 8 (CW2 x); bv_extract 32 8 (CW2 x); bv_extract 40 8 (CW2 x);
            bv_extract 48 8 (CW2 x); bv_extract 56 8 (CW2 x); z8; z8; x.8ₗ; x.9ₗ] ∗ K) -∗
  a ↦ₘ w -∗ (a + 8) ↦ₘ FW values -∗ (a + 16) ↦ₘ (BV 16 0) -∗ (a + 18) ↦ₘ? 2 -∗
  (∃ x : P2, a ↦ₘ∗ [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
            bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w;
            bv_extract 0 8 (CW2 x); bv_extract 8 8 (CW2 x); bv_extract 16 8 (CW2 x);
            bv_extract 24 8 (CW2 x); bv_extract 32 8 (CW2 x); bv_extract 40 8 (CW2 x);
            bv_extract 48 8 (CW2 x); bv_extract 56 8 (CW2 x); z8; z8; x.8ₗ; x.9ₗ] ∗ K).
Proof.
  iIntros "HG H0 H1 H2 H3".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist).
  iExact "HG".
Qed.

(* Refused: a gap; a piece that goes past the requested length; a closed
   requested byte that is not the held one; an array held at the address. *)
Notation P1 := (bv 8 *ₗ unit) (only parsing).

Lemma test_frame_fold_existential_gap `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  (∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K) -∗
  a ↦ₘ (BV 64 0) -∗ (a + 9) ↦ₘ (BV 16 0) -∗
  ∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K.
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist).
  iExact "HG".
Qed.

Lemma test_frame_fold_existential_overshoot `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  (∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K) -∗
  a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ (BV 64 0) -∗
  ∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K.
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist).
  iExact "HG".
Qed.

Lemma test_frame_fold_existential_other_bytes `{!islaG Sigma} (a : Z) (y : bv 64) (K : iProp Sigma) :
  (∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K) -∗
  a ↦ₘ y -∗ (a + 8) ↦ₘ (BV 16 0) -∗
  ∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K.
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist).
  iExact "HG".
Qed.

(* The successor's existential also binds components the list does not fix
   (decodeParentHeader 0514_slot3: seven padding bytes, then four 40-byte
   frame arrays and two words that later resources and facts mention). Only
   the padding byte the list exposes is instantiated; the other components
   stay existential in the residual goal (without this the fold refused the
   step: its witness kept evars). *)
Lemma test_frame_fold_existential_unfixed_components `{!islaG Sigma} (a : Z) (l : list (bv 8))
    (K : iProp Sigma) :
  a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ (BV 16 0) -∗ (a + 16) ↦ₘ∗ l -∗ K -∗
  ∃ x : bv 8 *ₗ list (bv 8) *ₗ bv 64 *ₗ unit,
    a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗
    ((a + 16) ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = length l⌝ ∗ ⌜x.1ₗ = bv_extract 8 8 (BV 16 0)⌝ ∗
     ⌜x.3ₗ = BV 64 0⌝ ∗ K).
Proof.
  iIntros "H0 H1 Hl HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist.
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ (list (bv 8) *ₗ bv 64 *ₗ unit) _) => idtac
  end.
  iExists (li_pair l (li_pair (BV 64 0) tt)). cbv [li_fst li_snd]. iFrame.
  repeat iSplit; iPureIntro; reflexivity.
Qed.
Print Assumptions test_frame_fold_existential_unfixed_components.

(* After the fold the successor's flag-word fact reads (0514_slot3 leftover):
   the held word against the concatenation of its own bytes 7 .. 1 over the
   flag, the flag being the first element of the word's little-endian list.
   `bv_solve` does not close it; the block tail does, through
   `WrappedWord.zesu_word_own_bytes_goal`; with another low byte, another
   word's bytes, or a side that is neither a variable nor a little-endian
   word it is refused. *)
Local Notation W values := (Z_to_bv 64 (little_endian_to_bv 8 (BV 8 1 :: take 7 values))) (only parsing).
Local Notation OWN values lo := (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40
    (bv_concat 32 (bv_concat 24 (bv_concat 16 (bv_extract 56 8 (W values)) (bv_extract 48 8 (W values)))
    (bv_extract 40 8 (W values))) (bv_extract 32 8 (W values))) (bv_extract 24 8 (W values)))
    (bv_extract 16 8 (W values))) (bv_extract 8 8 (W values))) lo) (only parsing).
Lemma test_word_concat_own_bytes (values : list (bv 8)) (H : length values = 15%nat) :
  W values = OWN values (BV 8 1).
Proof.
  assert_fails (idtac; solve [bv_solve]).
  ZesuSsz.Automation2.Finish.zesu_block_tail_one.
Qed.

(* The fold with the flag-word fact in the successor's package: the fold
   instantiates the seven padding bytes with the held word's bytes, the fact
   at that witness is left to the block tail. *)
Notation P7 := (bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ bv 8 *ₗ unit) (only parsing).
Lemma test_frame_fold_flag_word_fact `{!islaG Sigma} (a : Z) (values : list (bv 8)) (K : iProp Sigma) :
  a ↦ₘ W values -∗ (a + 8) ↦ₘ (BV 16 0) -∗ K -∗
  ∃ x : P7,
    a ↦ₘ∗ [BV 8 1; x.1ₗ; x.2ₗ; x.3ₗ; x.4ₗ; x.5ₗ; x.6ₗ; x.7ₗ; z8; z8] ∗
    ⌜W values = bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32
      (bv_concat 24 (bv_concat 16 x.7ₗ x.6ₗ) x.5ₗ) x.4ₗ) x.3ₗ) x.2ₗ) x.1ₗ) (BV 8 1)⌝ ∗ K.
Proof.
  iIntros "H0 H1 HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist.
  cbv [li_fst li_snd]. iFrame. iPureIntro.
  assert_fails (idtac; solve [bv_solve]).
  ZesuSsz.Automation2.Finish.zesu_block_tail_one.
Qed.
Print Assumptions test_frame_fold_flag_word_fact.

Lemma test_word_own_bytes_other_word (w v : bv 64) :
  let G := w = bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (bv_extract 56 8 v) (bv_extract 48 8 v)) (bv_extract 40 8 v)) (bv_extract 32 8 v))
    (bv_extract 24 8 v)) (bv_extract 16 8 v)) (bv_extract 8 8 v)) (bv_extract 0 8 v) in
  G -> G.
Proof.
  intros G Heq. unfold G in *.
  assert_fails (idtac; ZesuSsz.Automation2.WrappedWord.zesu_word_own_bytes_goal).
  exact Heq.
Qed.
Lemma test_word_own_bytes_other_list (values others : list (bv 8)) :
  W values = OWN others (BV 8 1) -> W values = OWN others (BV 8 1).
Proof.
  intros Heq.
  assert_fails (idtac; ZesuSsz.Automation2.WrappedWord.zesu_word_own_bytes_goal).
  exact Heq.
Qed.
(* Head test: the identity holds for every word, but a side that is neither a
   variable nor a little-endian word is refused before any check. *)
Lemma test_word_own_bytes_head_refused (w v : bv 64) :
  bv_add w v = bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (bv_extract 56 8 (bv_add w v)) (bv_extract 48 8 (bv_add w v))) (bv_extract 40 8 (bv_add w v)))
    (bv_extract 32 8 (bv_add w v))) (bv_extract 24 8 (bv_add w v))) (bv_extract 16 8 (bv_add w v)))
    (bv_extract 8 8 (bv_add w v))) (bv_extract 0 8 (bv_add w v)).
Proof.
  assert_fails (idtac; ZesuSsz.Automation2.WrappedWord.zesu_word_own_bytes_goal).
  ZesuSsz.Automation2.WrappedWord.zesu_word_concat_own_bytes_eq.
Qed.
Lemma test_word_concat_own_bytes_extract (w : bv 64) :
  w = bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (bv_extract 56 8 w) (bv_extract 48 8 w)) (bv_extract 40 8 w)) (bv_extract 32 8 w))
    (bv_extract 24 8 w)) (bv_extract 16 8 w)) (bv_extract 8 8 w)) (bv_extract 0 8 w).
Proof. ZesuSsz.Automation2.WrappedWord.zesu_word_concat_own_bytes_eq. Qed.
Lemma test_word_concat_own_bytes_other_flag (values : list (bv 8)) :
  W values = OWN values (BV 8 2) -> W values = OWN values (BV 8 2).
Proof.
  intros Heq.
  assert_fails (idtac; ZesuSsz.Automation2.WrappedWord.zesu_word_concat_own_bytes_eq).
  exact Heq.
Qed.

Lemma test_frame_fold_existential_array_held `{!islaG Sigma} (a : Z) (l : list (bv 8)) (K : iProp Sigma) :
  (∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K) -∗
  a ↦ₘ∗ l -∗ a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ (BV 16 0) -∗
  ∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K.
Proof.
  iIntros "HG Hl H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist).
  iExact "HG".
Qed.

(* The positive twin of the refusals: the same request over a held word whose
   bytes are those requested fires. *)
Lemma test_frame_fold_existential_fires_small `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ (BV 16 0) -∗ K -∗
  ∃ x : P1, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ (⌜x.1ₗ = bv_extract 8 8 (BV 16 0)⌝ ∗ K).
Proof.
  iIntros "H0 H1 HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist.
  cbv [li_fst li_snd]. iFrame. by iPureIntro.
Qed.
