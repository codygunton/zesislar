Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Import ListNotations.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A return through a register value saved in a byte frame: the target is the
   word of the eight extracted bytes of r, masked with ~1. The entry states
   that r is even, so the jump meets the contract at r and needs no code
   lookup. *)
Lemma return_saved_word `{!islaG Sigma} `{!threadG} (r : bv 64) :
  bv_unsigned r mod 2 = 0 ->
  "PC" ↦ᵣ RVal_Bits (bv_or (bv_and (bv_add (Z_to_bv 64 (little_endian_to_bv 8
      [bv_extract 0 8 r; bv_extract 8 8 r; bv_extract 16 8 r; bv_extract 24 8 r;
       bv_extract 32 8 r; bv_extract 40 8 r; bv_extract 48 8 r; bv_extract 56 8 r]))
    (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)) ∗
  instr_pre (bv_unsigned r) True -∗ WPasm tnil.
Proof. intros Heven. iIntros "[HPC Hpre]". zesu_block2. Qed.

(* The same when the entry states alignment to four bytes. *)
Lemma return_saved_word_aligned `{!islaG Sigma} `{!threadG} (r : bv 64) :
  bv_unsigned r mod 4 = 0 ->
  "PC" ↦ᵣ RVal_Bits (bv_or (bv_and (bv_add (Z_to_bv 64 (little_endian_to_bv 8
      [bv_extract 0 8 r; bv_extract 8 8 r; bv_extract 16 8 r; bv_extract 24 8 r;
       bv_extract 32 8 r; bv_extract 40 8 r; bv_extract 48 8 r; bv_extract 56 8 r]))
    (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)) ∗
  instr_pre (bv_unsigned r) True -∗ WPasm tnil.
Proof. intros Haligned. iIntros "[HPC Hpre]". zesu_block2. Qed.
