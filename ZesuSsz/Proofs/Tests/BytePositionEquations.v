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

Record WindowFrame := { windowPointer : bv 64 }.
Definition windowFrameWellFormed (frame : WindowFrame) : Prop :=
  (4096 <= bv_unsigned (windowPointer frame))%Z /\
  (bv_unsigned (windowPointer frame) < 4294967296)%Z.

(* A branch fact on the halfword at w - 360 of an array at w - 392, while the
   goal reads the array by byte positions: the fact's index becomes a literal,
   then its window the concatenation. *)
Goal forall frame (bytes : list (bv 8)), windowFrameWellFormed frame ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2)
    (drop (Z.to_nat (bv_unsigned (windowPointer frame + BV 64 18446744073709551216 +
      BV 64 400 + BV 64 18446744073709551256) -
      (bv_unsigned (windowPointer frame) - 400 + 8))) bytes)))) <> BV 64 0 ->
  bv_zero_extend 64 (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) <> BV 64 0.
Proof.
  intros frame bytes Hframe Hfact.
  zesu_le_window_rewrite_hypothesis.
  zesu_le_window_rewrite_hypothesis.
  exact Hfact.
Qed.

(* The residual shape of a branch: the final finisher states the fact the
   way the goal does (byte positions, then the bv_unsigned of the extended
   value) and closes the equation and the disequation. *)
Goal forall frame (bytes : list (bv 8)), windowFrameWellFormed frame ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2)
    (drop (Z.to_nat (bv_unsigned (windowPointer frame + BV 64 18446744073709551216 +
      BV 64 400 + BV 64 18446744073709551256) -
      (bv_unsigned (windowPointer frame) - 400 + 8))) bytes)))) = BV 64 0 ->
  bv_unsigned (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) = 0%Z.
Proof. intros frame bytes Hframe Hfact. zesu_byte_position_facts. assumption. Qed.

Goal forall frame (bytes : list (bv 8)), windowFrameWellFormed frame ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2)
    (drop (Z.to_nat (bv_unsigned (windowPointer frame + BV 64 18446744073709551216 +
      BV 64 400 + BV 64 18446744073709551256) -
      (bv_unsigned (windowPointer frame) - 400 + 8))) bytes)))) <> BV 64 0 ->
  bv_unsigned (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) <> 0%Z.
Proof. intros frame bytes Hframe Hfact. zesu_finish_final_pure. Qed.

(* A word fact on a value the goal does not state: it stays. *)
Goal forall (value : bv 16), bv_zero_extend 64 value = BV 64 0 -> True.
Proof. intros value Hfact. Fail zesu_word_fact_unsigned. exact I. Qed.

(* A zero-extended word fact: the width condition is closed, so the view is
   stated from the fact alone. *)
Goal forall (value : bv 16), bv_zero_extend 64 value = BV 64 0 ->
  bv_unsigned value = 0%Z.
Proof. intros value Hfact. zesu_word_fact_unsigned. exact Hview. Qed.

(* A narrowing "extension" is refused by computing the widths, never by
   searching the context: a contradictory hypothesis does not admit it. *)
Goal forall (value : bv 64), (0 = 1)%nat -> @bv_zero_extend 64 16 value = BV 16 0 ->
  bv_unsigned value = 0%Z -> True.
Proof.
  intros value Hcontra Hfact Hgoal. revert Hgoal.
  Fail zesu_word_fact_unsigned.
  intros _. exact I.
Qed.

(* A branch fact on a byte variable known from a lookup, while the goal reads
   the byte's position: the fact moves to the position, then to bv_unsigned. *)
Goal forall (bytes : list (bv 8)) (value : bv 8), bytes !! 16%nat = Some value ->
  bv_and (bv_zero_extend 64 value) (BV 64 1) = BV 64 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (nth 16 bytes (BV 8 0))) (BV 64 1)) = 0%Z.
Proof. intros bytes value Hlookup Hfact. zesu_finish_final_pure. Qed.

Goal forall (bytes : list (bv 8)) (value : bv 8), bytes !! 16%nat = Some value ->
  bv_and (bv_zero_extend 64 value) (BV 64 1) <> BV 64 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (nth 16 bytes (BV 8 0))) (BV 64 1)) <> 0%Z.
Proof. intros bytes value Hlookup Hfact. zesu_byte_position_facts. assumption. Qed.

(* The goal reads another position: the fact stays. *)
Goal forall (bytes : list (bv 8)) (value : bv 8), bytes !! 16%nat = Some value ->
  bv_and (bv_zero_extend 64 value) (BV 64 1) = BV 64 0 ->
  bv_unsigned (nth 17 bytes (BV 8 0)) = 0%Z -> True.
Proof. intros bytes value Hlookup Hfact. Fail zesu_lookup_value_rewrite_hypothesis. intros _. exact I. Qed.

(* The goal does not read the list: the fact stays. *)
Goal forall (bytes : list (bv 8)),
  Z_to_bv 16 (little_endian_to_bv 8 (take 2 (drop 32 bytes))) = BV 16 0 -> True.
Proof. intros bytes Hfact. Fail zesu_le_window_rewrite_hypothesis. exact I. Qed.

(* Guard conjuncts that the package split makes after the final pure step.
   The branch facts are older than the split (no fact after the baseline
   reaches the conjunct), so only their byte-position view closes it. *)
Goal forall (bytes : list (bv 8)),
  bv_zero_extend 64 (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) = BV 64 0 ->
  bv_unsigned (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) = 0%Z.
Proof.
  intros bytes Hfact.
  pose proof ZesuSsz.Automation2.Finish.zesu_split_baseline_intro as Hbaseline.
  ZesuSsz.Automation2.Finish.zesu_finish_split_conjunct.
Qed.

Goal forall frame (bytes : list (bv 8)), windowFrameWellFormed frame ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2)
    (drop (Z.to_nat (bv_unsigned (windowPointer frame + BV 64 18446744073709551216 +
      BV 64 400 + BV 64 18446744073709551256) -
      (bv_unsigned (windowPointer frame) - 400 + 8))) bytes)))) <> BV 64 0 ->
  bv_unsigned (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) <> 0%Z.
Proof.
  intros frame bytes Hframe Hfact.
  pose proof ZesuSsz.Automation2.Finish.zesu_split_baseline_intro as Hbaseline.
  ZesuSsz.Automation2.Finish.zesu_finish_split_conjunct.
Qed.

(* The conjunct reads another position: the split conjunct stays open. *)
Goal forall (bytes : list (bv 8)),
  bv_zero_extend 64 (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))) = BV 64 0 ->
  True.
Proof.
  intros bytes Hfact.
  pose proof ZesuSsz.Automation2.Finish.zesu_split_baseline_intro as Hbaseline.
  Fail assert (bv_unsigned (bv_concat 16 (nth 35 bytes (BV 8 0)) (nth 34 bytes (BV 8 0))) = 0%Z)
    by ZesuSsz.Automation2.Finish.zesu_finish_split_conjunct.
  exact I.
Qed.

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
