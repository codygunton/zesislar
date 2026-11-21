From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
From stdpp Require Import list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The reload step before the extract-window branch: only a window of
   masked integer bytes was read back. *)
Ltac previous_reload_encoded_word_step :=
  match goal with
  | |- context [Z_to_bv ?width
        (little_endian_to_bv 8 (take ?count (drop (Z.to_nat ?offset) ?bytes)))] =>
      assert_fails (has_evar bytes);
      let value := ByteWordReload.zesu_reload_constant offset in
      let index := eval vm_compute in (Z.to_nat value) in
      let size := eval vm_compute in count in
      let window := eval cbn [take drop] in (take size (drop index bytes)) in
      lazymatch window with
      | Z_to_bv 8 (Z.land ?word (Z.ones 8)) :: _ =>
          let Hreload := fresh "HreloadByteWord" in
          assert (Hreload : Z_to_bv width
              (little_endian_to_bv 8 (take count (drop (Z.to_nat offset) bytes))) =
            Z_to_bv width word) by (
            replace offset with value by (clear; zesu_lia);
            change (take count (drop (Z.to_nat value) bytes)) with window;
            change window with (bv_to_little_endian size 8 word);
            apply ByteWordReload.zesu_reload_byte_word;
            [first [apply (proj1 (bv_unsigned_in_range _ _)) | zesu_lia] | vm_compute; reflexivity]);
          rewrite Hreload; clear Hreload
      end
  end.

(* A word saved byte-wise into a frame slot, one byte after the slot base,
   and read back as a word. *)
Lemma reload_extract_word (frame : Z) (b : bv 8) (word : bv 64) (rest : list (bv 8)) :
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat (frame + 1 - frame))
    (b :: bv_extract 0 8 word :: bv_extract 8 8 word :: bv_extract 16 8 word ::
     bv_extract 24 8 word :: bv_extract 32 8 word :: bv_extract 40 8 word ::
     bv_extract 48 8 word :: bv_extract 56 8 word :: rest)))) = word.
Proof.
  Fail ByteWordReload.zesu_reload_spliced_word_step.
  Fail previous_reload_encoded_word_step.
  ByteWordReload.zesu_reload_encoded_word_step.
  reflexivity.
Qed.

(* A four-byte word. *)
Lemma reload_extract_word32 (word : bv 32) (rest : list (bv 8)) :
  Z_to_bv 32 (little_endian_to_bv 8 (take 4 (drop (Z.to_nat 0)
    (bv_extract 0 8 word :: bv_extract 8 8 word :: bv_extract 16 8 word ::
     bv_extract 24 8 word :: rest)))) = word.
Proof.
  Fail previous_reload_encoded_word_step.
  ByteWordReload.zesu_reload_byte_word_step.
  reflexivity.
Qed.

(* The read width differs from the saved word's width: refused. *)
Lemma reload_extract_width_mismatch (word : bv 64) (rest : list (bv 8)) : True.
Proof.
  Fail assert (Hbad : Z_to_bv 32 (little_endian_to_bv 8 (take 4 (drop (Z.to_nat 0)
    (bv_extract 0 8 word :: bv_extract 8 8 word :: bv_extract 16 8 word ::
     bv_extract 24 8 word :: rest)))) = Z_to_bv 32 (bv_unsigned word))
    by (ByteWordReload.zesu_reload_encoded_word_step; reflexivity).
  exact I.
Qed.

(* The window skips the first extract: the bytes are not the word. *)
Lemma reload_extract_misaligned_window (word : bv 64) (b : bv 8) : True.
Proof.
  Fail assert (Hbad : Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat 1)
    (bv_extract 0 8 word :: bv_extract 8 8 word :: bv_extract 16 8 word ::
     bv_extract 24 8 word :: bv_extract 32 8 word :: bv_extract 40 8 word ::
     bv_extract 48 8 word :: bv_extract 56 8 word :: b :: nil)))) = word)
    by (ByteWordReload.zesu_reload_encoded_word_step; reflexivity).
  exact I.
Qed.

(* A frame slot read back through a pointer the code moved down from the
   stack pointer (`sp - 400 + 400 - 344`), against the slot address spelled
   from the stack pointer itself (`sp - 400 + 56`): the offset is 0, which
   needs the range of the stack pointer (no wrap). Counting the bitvector sum
   as an atom guessed 344 and the step failed (decodeParentHeader 0570). *)
Lemma reload_extract_word_stack_sum (sp word : bv 64) (rest : list (bv 8)) :
  2684355072 <= bv_unsigned sp < 3221225472 ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat
    (bv_unsigned (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400))
       (BV 64 18446744073709551272)) - (bv_unsigned sp - 400 + 48 + 8)))
    (bv_extract 0 8 word :: bv_extract 8 8 word :: bv_extract 16 8 word ::
     bv_extract 24 8 word :: bv_extract 32 8 word :: bv_extract 40 8 word ::
     bv_extract 48 8 word :: bv_extract 56 8 word :: rest)))) = word.
Proof.
  intros Hsp.
  ByteWordReload.zesu_reload_byte_word_step.
  reflexivity.
Qed.

(* The guess of that offset: the literals count signed, the bases cancel. *)
Lemma reload_constant_stack_sum (sp : bv 64) : True.
Proof.
  let value := ByteWordReload.zesu_reload_constant
    (bv_unsigned (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400))
       (BV 64 18446744073709551272)) - (bv_unsigned sp - 400 + 48 + 8)) in
  assert (Hvalue : value = 0) by reflexivity.
  exact I.
Qed.

(* Without the stack pointer's range the sum may wrap: the guess is not
   proved and the step refuses. *)
Lemma reload_extract_word_stack_sum_unranged (sp word : bv 64) (rest : list (bv 8)) : True.
Proof.
  Fail assert (Hbad : Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat
    (bv_unsigned (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400))
       (BV 64 18446744073709551272)) - (bv_unsigned sp - 400 + 48 + 8)))
    (bv_extract 0 8 word :: bv_extract 8 8 word :: bv_extract 16 8 word ::
     bv_extract 24 8 word :: bv_extract 32 8 word :: bv_extract 40 8 word ::
     bv_extract 48 8 word :: bv_extract 56 8 word :: rest)))) = word)
    by (ByteWordReload.zesu_reload_byte_word_step; reflexivity).
  exact I.
Qed.

Print Assumptions reload_extract_word.
Print Assumptions reload_extract_word32.
Print Assumptions reload_extract_word_stack_sum.
