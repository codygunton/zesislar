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
   requested byte that is not the held one; an existential component the list
   does not fix (not forced); an array held at the address. *)
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

Lemma test_frame_fold_existential_unforced `{!islaG Sigma} (a : Z) (K : iProp Sigma) :
  (∃ x : bv 8 *ₗ bv 8 *ₗ unit, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K) -∗
  a ↦ₘ (BV 64 0) -∗ (a + 8) ↦ₘ (BV 16 0) -∗
  ∃ x : bv 8 *ₗ bv 8 *ₗ unit, a ↦ₘ∗ [z8; z8; z8; z8; z8; z8; z8; z8; z8; x.1ₗ] ∗ K.
Proof.
  iIntros "HG H0 H1".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_join_frame_explicit_exist).
  iExact "HG".
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
