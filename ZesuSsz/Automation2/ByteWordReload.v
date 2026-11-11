From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
From stdpp Require Import list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require ZesuSsz.Automation2.ContextCollection.
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

(* Zero every atom of a linear integer expression. *)
Ltac zesu_reload_zero_atoms term :=
  lazymatch term with
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
          ("reload.spliced_index"%string) ltac:(lia)]);
      assert (Hinside : (stored <= length bytes)%nat) by
        (ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
          ("reload.spliced_bound"%string) ltac:(lia));
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
            replace offset with value by (clear; lia);
            change (take count (drop (Z.to_nat value) bytes)) with window;
            change window with (bv_to_little_endian size 8 word);
            apply zesu_reload_byte_word;
            [first [apply (proj1 (bv_unsigned_in_range _ _)) | lia] | vm_compute; reflexivity]);
          rewrite Hreload; clear Hreload
      end
  end.

Ltac zesu_reload_byte_word_step :=
  first [zesu_reload_spliced_word_step | zesu_reload_encoded_word_step].
