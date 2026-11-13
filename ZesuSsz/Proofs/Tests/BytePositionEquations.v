From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A little-endian window of c bytes at k becomes the concatenation of the
   bytes at k + c - 1 .. k, the form the specs state. *)
Goal forall (bytes : list (bv 8)),
  Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 bytes))) =
  bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0)).
Proof. intros bytes. zesu_le_window_rewrite_one. reflexivity. Qed.

Goal forall (bytes : list (bv 8)),
  Z_to_bv 32 (little_endian_to_bv 8 (take 4 (drop 3 bytes))) =
  bv_concat 32 (bv_concat 24 (bv_concat 16 (nth 6 bytes (BV 8 0)) (nth 5 bytes (BV 8 0)))
    (nth 4 bytes (BV 8 0))) (nth 3 bytes (BV 8 0)).
Proof. intros bytes. zesu_le_window_rewrite_one. reflexivity. Qed.

(* A window wider than its bytes has no concatenation form: no rewrite. *)
Goal forall (bytes : list (bv 8)),
  Z_to_bv 64 (little_endian_to_bv 8 (take 2 (drop 32 bytes))) = Z_to_bv 64 0 -> True.
Proof. intros bytes. Fail zesu_le_window_rewrite_one. intros _. exact I. Qed.

(* A window at an open start has no fixed byte positions: no rewrite. *)
Goal forall (bytes : list (bv 8)) (address : bv 64),
  Z_to_bv 16 (little_endian_to_bv 8 (take 2 (drop (Z.to_nat (bv_unsigned address)) bytes))) =
  Z_to_bv 16 0 -> True.
Proof. intros bytes address. Fail zesu_le_window_rewrite_one. intros _. exact I. Qed.

Definition byte_outcome : Type := list (bv 8).

Section lazy_existential.
  Context `{!islaG Sigma}.

  (* The spec reads two bytes of an existential list; the state holds the
     window. Lithium alone stops; after the step, unification sets the list. *)
  Goal forall (bytes : list (bv 8)) (R : list (bv 8) -> iProp Sigma),
    R bytes ⊢ ∃ (other : bv 64) (list_value : list (bv 8)),
      ⌜bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 bytes)))) =
       bv_zero_extend 64 (bv_concat 16 (nth 33 list_value (BV 8 0)) (nth 32 list_value (BV 8 0)))⌝ ∗
      R list_value.
  Proof.
    intros bytes R. iStartProof. iIntros "HR".
    repeat liExist.
    Fail liSideCond.
    zesu_byte_position_pure_step.
    liSideCond.
    lazymatch goal with |- environments.envs_entails _ (∃ _ : unit, R bytes) => idtac end.
    iExists tt. iExact "HR".
  Qed.

  (* The state holds a byte variable with its lookup fact. *)
  Goal forall (bytes : list (bv 8)) (value : bv 8) (R : list (bv 8) -> iProp Sigma),
    bytes !! 16%nat = Some value ->
    R bytes ⊢ ∃ (other : bv 64) (list_value : list (bv 8)),
      ⌜bv_and (bv_zero_extend 64 value) (BV 64 1) =
       bv_and (bv_zero_extend 64 (nth 16 list_value (BV 8 0))) (BV 64 1)⌝ ∗ R list_value.
  Proof.
    intros bytes value R Hvalue. iStartProof. iIntros "HR".
    repeat liExist.
    Fail liSideCond.
    zesu_byte_position_pure_step.
    liSideCond.
    lazymatch goal with |- environments.envs_entails _ (∃ _ : unit, R bytes) => idtac end.
    iExists tt. iExact "HR".
  Qed.

  (* The state holds the window behind trace lets, one for the loaded value
     and one for its address, over a list typed by an alias. *)
  Goal forall (bytes : byte_outcome) (R : byte_outcome -> iProp Sigma),
    let address := bv_add (BV 64 4096) (BV 64 40) in
    let loaded := bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8
      (take (N.to_nat 2) (drop (Z.to_nat (bv_unsigned address - 4104)) bytes)))) in
    R bytes ⊢ ∃ (other : bv 64) (list_value : byte_outcome),
      ⌜loaded =
       bv_zero_extend 64 (bv_concat 16 (nth 33 list_value (BV 8 0)) (nth 32 list_value (BV 8 0)))⌝ ∗
      R list_value.
  Proof.
    intros bytes R address loaded. iStartProof. iIntros "HR".
    repeat liExist.
    Fail liSideCond.
    zesu_byte_position_pure_step.
    liSideCond.
    lazymatch goal with |- environments.envs_entails _ (∃ _ : unit, R bytes) => idtac end.
    iExists tt. iExact "HR".
  Qed.
End lazy_existential.

(* A byte variable with a lookup fact at the position the goal reads becomes
   that position. *)
Goal forall (bytes : list (bv 8)) (value : bv 8), bytes !! 16%nat = Some value ->
  (bv_and (bv_zero_extend 64 value) (BV 64 1) =
   bv_and (bv_zero_extend 64 (nth 16 bytes (BV 8 0))) (BV 64 1)) =
  (bv_and (bv_zero_extend 64 (nth 16 bytes (BV 8 0))) (BV 64 1) =
   bv_and (bv_zero_extend 64 (nth 16 bytes (BV 8 0))) (BV 64 1)).
Proof. intros bytes value Hvalue. zesu_lookup_value_rewrite_one. reflexivity. Qed.

(* A lookup fact at another position: no rewrite. *)
Goal forall (bytes : list (bv 8)) (value : bv 8), bytes !! 17%nat = Some value ->
  (bv_and (bv_zero_extend 64 value) (BV 64 1) =
   bv_and (bv_zero_extend 64 (nth 16 bytes (BV 8 0))) (BV 64 1)) =
  (bv_and (bv_zero_extend 64 value) (BV 64 1) =
   bv_and (bv_zero_extend 64 (nth 16 bytes (BV 8 0))) (BV 64 1)).
Proof. intros bytes value Hvalue. Fail zesu_lookup_value_rewrite_one. reflexivity. Qed.
