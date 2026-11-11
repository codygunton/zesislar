Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A store spliced a word's little-endian bytes into a byte-array frame at
   index i; a load of the same slice must give the word back. *)
Lemma spliced_word_reload (xs : list (bv 8)) (i : nat) (w : bv 64) :
  (i + 8 <= length xs)%nat ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop i
    (take i xs ++ bv_to_little_endian 8 8 (bv_unsigned w) ++ drop (i + 8) xs)))) = w.
Proof. intros Hlength. zesu_block2. Qed.

(* The index is the offset of the stored address from the array base. *)
Lemma spliced_word_reload_address `{!islaG Sigma} `{!threadG}
    (xs : list (bv 8)) (p base w : bv 64) (R : iProp Sigma) :
  (Z.to_nat (bv_unsigned p - bv_unsigned base) + 8 <= length xs)%nat ->
  R -∗ (⌜Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat (bv_unsigned p - bv_unsigned base))
    (take (Z.to_nat (bv_unsigned p - bv_unsigned base)) xs ++ bv_to_little_endian 8 8 (bv_unsigned w) ++
     drop (Z.to_nat (bv_unsigned p - bv_unsigned base) + 8) xs)))) = w⌝ ∗ R).
Proof. intros Hlength. iIntros "HR". zesu_block2. Qed.

(* A saved register at offset 8 of a 16-byte frame. *)
Lemma spliced_word_reload_frame `{!islaG Sigma} `{!threadG} (xs : list (bv 8)) (w : bv 64) (R : iProp Sigma) :
  length xs = 16%nat ->
  R -∗ (⌜Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat 8)
    (take 8 xs ++ bv_to_little_endian 8 8 (bv_unsigned w) ++ drop (8 + 8) xs)))) = w⌝ ∗ R).
Proof. intros Hlength. iIntros "HR". zesu_block2. Qed.
