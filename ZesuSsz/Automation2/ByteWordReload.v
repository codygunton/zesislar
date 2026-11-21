From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
From stdpp Require Import list bitvector.definitions bitvector.tactics.
Require Import isla.riscv64.riscv64.
Require ZesuSsz.Automation2.ContextCollection.
Require ZesuSsz.Automation2.ByteExtractCodec281.
Require Import ZesuSsz.Automation2.LiaHook.
Local Open Scope Z_scope.

(* A word read back from the little-endian bytes of a stored word is that word. *)
Lemma zesu_reload_byte_word (width : N) (count : nat) (word : Z) :
  0 <= word -> width = (N.of_nat count * 8)%N ->
  Z_to_bv width (little_endian_to_bv 8 (bv_to_little_endian count 8 word)) =
  Z_to_bv width word.
Proof.
  intros Hword ->. rewrite little_endian_to_bv_to_little_endian; [|lia].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  replace (Z.of_nat count * Z.of_N 8) with (Z.of_N (N.of_nat count * 8)) by lia.
  rewrite Z.mod_mod; [reflexivity|].
  apply Z.pow_nonzero; lia.
Qed.

(* A store splices a word's little-endian bytes into a byte array at an
   index; a load of the same slice reads the word back. *)
Lemma zesu_reload_spliced_word (xs tail : list (bv 8)) (stored loaded : nat) (word : bv 64) :
  loaded = stored -> (stored <= length xs)%nat ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop loaded
    (take stored xs ++ bv_to_little_endian 8 8 (bv_unsigned word) ++ tail)))) = word.
Proof.
  intros -> Hstored.
  rewrite drop_app_length'; [| rewrite length_take_le; [reflexivity | exact Hstored]].
  rewrite take_app_length'; [| rewrite length_bv_to_little_endian; lia].
  apply Z_to_bv_little_endian_to_bv_to_little_endian; [lia | reflexivity].
Qed.

(* A word read back from the extracted bytes of a word saved byte-wise
   (a frame slot) is that word. *)
Lemma zesu_reload_extract_word (width : N) (count : nat) (word : bv width) :
  width = (N.of_nat count * 8)%N ->
  Z_to_bv width (little_endian_to_bv 8
    (ZesuSsz.Automation2.ByteExtractCodec281.byte_extracts281 count word)) = word.
Proof.
  intros Hwidth.
  rewrite ZesuSsz.Automation2.ByteExtractCodec281.byte_extracts_codec281.
  apply Z_to_bv_little_endian_to_bv_to_little_endian; [lia | subst width; lia].
Qed.

(* The guess for a bitvector sum read as an integer: its base counts zero and
   each literal its signed value, so `bv_unsigned (sp + BV 64 (2^64 - 344))`
   counts -344 (a pointer moved down from the stack pointer, the base the
   other side of the offset spells as `bv_unsigned sp`). The guess assumes
   no wrap; the caller proves it. *)
Ltac zesu_reload_bv_sum term :=
  lazymatch term with
  | bv_add ?left ?right =>
      let l := zesu_reload_bv_sum left in let r := zesu_reload_bv_sum right in
      constr:((l + r)%Z)
  | @BV ?n ?c _ =>
      eval vm_compute in (if Z.ltb c (2 ^ (Z.of_N n - 1)) then c else (c - 2 ^ Z.of_N n)%Z)
  | _ => constr:(0%Z)
  end.

(* Zero every atom of a linear integer expression; the integer value of a
   bitvector sum is guessed by `zesu_reload_bv_sum`. *)
Ltac zesu_reload_zero_atoms term :=
  lazymatch term with
  | bv_unsigned (bv_add ?left ?right) => zesu_reload_bv_sum (bv_add left right)
  | (?left + ?right)%Z =>
      let l := zesu_reload_zero_atoms left in let r := zesu_reload_zero_atoms right in
      constr:((l + r)%Z)
  | (?left - ?right)%Z =>
      let l := zesu_reload_zero_atoms left in let r := zesu_reload_zero_atoms right in
      constr:((l - r)%Z)
  | (?left * ?right)%Z =>
      let l := zesu_reload_zero_atoms left in let r := zesu_reload_zero_atoms right in
      constr:((l * r)%Z)
  | (- ?value)%Z => let v := zesu_reload_zero_atoms value in constr:((- v)%Z)
  | Z.of_nat O => term
  | Z.of_nat (S _) => term
  | Z0 => term
  | Zpos _ => term
  | Zneg _ => term
  | _ => constr:(0%Z)
  end.

(* The value of an offset whose atoms cancel; the caller proves it by lia. *)
Ltac zesu_reload_constant offset :=
  let zeroed := zesu_reload_zero_atoms offset in
  eval vm_compute in zeroed.

(* The offset equals its guessed value: by lia on the offset alone, else
   (a bitvector sum, which needs the base's range to exclude a wrap) by
   `bv_solve` on the facts that share its terms. *)
Ltac zesu_reload_offset_value offset value :=
  replace offset with value by (first [clear; zesu_lia |
    lazymatch offset with context [bv_unsigned (bv_add _ _)] => idtac end;
    ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
      ("reload.encoded_offset"%string) ltac:(bv_solve)]).

(* The load index equals the store index, and the store index lies inside
   the array; both are read from the facts that share their terms. *)
Ltac zesu_reload_spliced_word_step :=
  match goal with
  | |- context [Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop ?loaded
        (take ?stored ?bytes ++ bv_to_little_endian 8 8 (bv_unsigned ?word) ++ ?tail))))] =>
      assert_fails (has_evar bytes); assert_fails (has_evar word);
      assert_fails (has_evar loaded); assert_fails (has_evar stored);
      let Hsame := fresh "HreloadSameIndex" in
      let Hinside := fresh "HreloadInside" in
      assert (Hsame : loaded = stored) by
        (first [reflexivity | ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
          ("reload.spliced_index"%string) ltac:(zesu_lia)]);
      assert (Hinside : (stored <= length bytes)%nat) by
        (ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
          ("reload.spliced_bound"%string) ltac:(zesu_lia));
      rewrite (zesu_reload_spliced_word bytes tail stored loaded word Hsame Hinside);
      clear Hsame Hinside
  end.

Ltac zesu_reload_encoded_word_step :=
  match goal with
  | |- context [Z_to_bv ?width
        (little_endian_to_bv 8 (take ?count (drop (Z.to_nat ?offset) ?bytes)))] =>
      assert_fails (has_evar bytes);
      let value := zesu_reload_constant offset in
      let index := eval vm_compute in (Z.to_nat value) in
      let size := eval vm_compute in count in
      let window := eval cbn [take drop] in (take size (drop index bytes)) in
      lazymatch window with
      | Z_to_bv 8 (Z.land ?word (Z.ones 8)) :: _ =>
          let Hreload := fresh "HreloadByteWord" in
          assert (Hreload : Z_to_bv width
              (little_endian_to_bv 8 (take count (drop (Z.to_nat offset) bytes))) =
            Z_to_bv width word) by (
            zesu_reload_offset_value offset value;
            change (take count (drop (Z.to_nat value) bytes)) with window;
            change window with (bv_to_little_endian size 8 word);
            apply zesu_reload_byte_word;
            [first [apply (proj1 (bv_unsigned_in_range _ _)) | zesu_lia] | vm_compute; reflexivity]);
          rewrite Hreload; clear Hreload
      | bv_extract 0 8 ?word :: _ =>
          lazymatch type of word with bv width => idtac end;
          let Hreload := fresh "HreloadExtractWord" in
          assert (Hreload : Z_to_bv width
              (little_endian_to_bv 8 (take count (drop (Z.to_nat offset) bytes))) = word) by (
            zesu_reload_offset_value offset value;
            change (take count (drop (Z.to_nat value) bytes)) with window;
            change window with (ZesuSsz.Automation2.ByteExtractCodec281.byte_extracts281 size word);
            apply zesu_reload_extract_word; vm_compute; reflexivity);
          rewrite Hreload; clear Hreload
      end
  end.

Ltac zesu_reload_byte_word_step :=
  first [zesu_reload_spliced_word_step | zesu_reload_encoded_word_step].
