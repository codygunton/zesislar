Require Import isla.riscv64.riscv64.
From stdpp Require Import list.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.LoadedTrace.

Definition loaded_word_bytes8 (word : bv 64) : list (bv 8) :=
  [Z_to_bv 8 (bv_unsigned word `mod` 256);
   Z_to_bv 8 ((bv_unsigned word `div` 256) `mod` 256);
   Z_to_bv 8 (((bv_unsigned word `div` 256) `div` 256) `mod` 256);
   Z_to_bv 8 ((((bv_unsigned word `div` 256) `div` 256) `div` 256) `mod` 256);
   Z_to_bv 8 (((((bv_unsigned word `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
   Z_to_bv 8 ((((((bv_unsigned word `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
   Z_to_bv 8 (((((((bv_unsigned word `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
   Z_to_bv 8 ((((((((bv_unsigned word `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)].

Lemma loaded_word_exact_eight_bytes (words : list (bv 64)) (index : nat)
    (fallback loaded : bv 64) (event : seq_event) (addr : Z) (tail : spec) :
  words !! index = Some loaded ->
  scons_snap event
    (λ snapshot, read_mem_list (snap_mem snapshot) addr 8 =
      Some (loaded_word_bytes8 loaded)) tail ⊆
  scons_snap event
    (λ snapshot, read_mem_list (snap_mem snapshot) addr 8 =
      Some (loaded_word_bytes8 (default fallback (words !! index)))) tail.
Proof.
  intros Hlookup.
  zesu_close_loaded_lookup.
Qed.

Lemma loaded_word_exact_eight_bytes_inline (words : list (bv 64)) (index : nat)
    (fallback loaded : bv 64) (event : seq_event) (addr : Z) (tail : spec) :
  words !! index = Some loaded ->
  scons_snap event
    (λ snapshot, read_mem_list (snap_mem snapshot) addr 8 =
      Some
        [Z_to_bv 8 (bv_unsigned (loaded) `mod` 256);
         Z_to_bv 8 ((bv_unsigned (loaded) `div` 256) `mod` 256);
         Z_to_bv 8 (((bv_unsigned (loaded) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 ((((bv_unsigned (loaded) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 (((((bv_unsigned (loaded) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 ((((((bv_unsigned (loaded) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 (((((((bv_unsigned (loaded) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 ((((((((bv_unsigned (loaded) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)]) tail ⊆
  scons_snap event
    (λ snapshot, read_mem_list (snap_mem snapshot) addr 8 =
      Some
        [Z_to_bv 8 (bv_unsigned (default fallback (words !! index)) `mod` 256);
         Z_to_bv 8 ((bv_unsigned (default fallback (words !! index)) `div` 256) `mod` 256);
         Z_to_bv 8 (((bv_unsigned (default fallback (words !! index)) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 ((((bv_unsigned (default fallback (words !! index)) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 (((((bv_unsigned (default fallback (words !! index)) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 ((((((bv_unsigned (default fallback (words !! index)) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 (((((((bv_unsigned (default fallback (words !! index)) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
         Z_to_bv 8 ((((((((bv_unsigned (default fallback (words !! index)) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)]) tail.
Proof.
  intros Hlookup.
  zesu_close_loaded_lookup.
Qed.

Print Assumptions zesu_scons_snap_loaded_lookup.
Print Assumptions loaded_word_exact_eight_bytes.
Print Assumptions loaded_word_exact_eight_bytes_inline.
