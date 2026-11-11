Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Local Open Scope Z_scope.

(* A call-return seed renders the caller's saved frame as the little-endian
   words of its stores (decodeItem's frame form). A load of any saved word
   reads that word back; the epilogue's ld ra then yields the return address. *)
Notation frameWord w := (bv_to_little_endian (Z.of_nat 8%nat) 8%N (bv_unsigned (w : bv 64%N))) (only parsing).

Lemma frame_word_reload_two (a w : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat 8) (frameWord a ++ frameWord w)))) = w.
Proof. zesu_block2. Qed.

Lemma frame_word_reload_last (a b c d e w : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat 40)
    (frameWord a ++ frameWord b ++ frameWord c ++ frameWord d ++ frameWord e ++ frameWord w)))) = w.
Proof. zesu_block2. Qed.

Lemma frame_word_reload_first (a b c d e w : bv 64) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat 0)
    (frameWord a ++ frameWord b ++ frameWord c ++ frameWord d ++ frameWord e ++ frameWord w)))) = a.
Proof. zesu_block2. Qed.
