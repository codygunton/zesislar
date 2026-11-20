From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A loop exit to a forward successor: the successor's ghost witnesses are
   constrained only by mask facts, and its other facts are views of the guards
   the loop decided (a signed compare of a zero-extended count, a word against
   zero). The zero tuple is committed, then every conjunct is a view. *)
Lemma loop_exit_zero_witnesses `{!islaG Σ} `{!threadG} (K : iProp Σ) (count mask : bv 64) :
  bool_decide (Z.land (bv_unsigned mask) 131072 = 0) = true ->
  count <> BV 64 0 ->
  bv_signed (BV 128 8) >= bv_signed (bv_zero_extend 128 count) ->
  K ⊢ ∃ x : bv 64 *ₗ bv 64 *ₗ (),
    ⌜bv_and (li_fst x) (BV 64 131072) = BV 64 0⌝ ∗
    ⌜negb (bool_decide (bv_extract 17 1 (li_fst (li_snd x)) = BV 1 1)) = true ∧
      bv_unsigned (bv_extract 17 1 (li_fst (li_snd x))) ≠ 1⌝ ∗
    ⌜bool_decide (bv_signed (BV 128 8) >= bv_signed (bv_zero_extend 128 count)) = true ∧
      8 >= bv_unsigned count⌝ ∗
    ⌜bv_unsigned count ≠ 0⌝ ∗ K.
Proof.
  intros Hmask Hcount Hguard. iIntros "HK".
  zesu_loop_exit_witnesses.
Qed.

(* Guard: a conjunct that no guard of the context gives as a view (here an
   order fact that needs arithmetic) refuses the exit step, so the zero
   witnesses are never committed by it for a goal it does not close. *)
Lemma loop_exit_refused `{!islaG Σ} `{!threadG} (K : iProp Σ) (count : bv 64) :
  count <> BV 64 0 ->
  K ⊢ ∃ x : bv 64 *ₗ (),
    ⌜bv_and (li_fst x) (BV 64 131072) = BV 64 0⌝ ∗
    ⌜bv_unsigned count < bv_unsigned count + 1⌝ ∗ K.
Proof.
  intros Hcount. iIntros "HK".
  Fail zesu_loop_exit_witnesses.
  iExists (li_pair (BV 64 0) tt).
  iSplit; [iPureIntro; apply bv_eq; reflexivity|].
  iSplit; [iPureIntro; cbn; lia|].
  iFrame.
Qed.

(* The list index of a cursor load: the goal counts at `bv 8`, the range
   fact at `byte`. Linear arithmetic sees two `length` atoms. *)
Lemma loop_cursor_index (input : list EvmSailRlp.evm_rlp_types.byte) (cursor : bv 64) (base : Z) :
  base <= bv_unsigned cursor < base + Z.of_nat (length input) ->
  (Z.to_nat ((bv_unsigned cursor - base) `div` 1) < @length (bv 8) input)%nat.
Proof.
  intros Hrange.
  Fail ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia.
  zesu_cursor_index_close.
Qed.

(* Guard: the range fact must be on the same cursor and base. *)
Goal forall (input : list (bv 8)) (cursor other : Z) (base : Z),
  base <= other < base + Z.of_nat (length input) ->
  cursor = other ->
  (Z.to_nat ((cursor - base) `div` 1) < length input)%nat.
Proof.
  intros input cursor other base Hrange Heq.
  Fail zesu_cursor_index_close.
  subst cursor. zesu_cursor_index_close.
Qed.

(* The views one by one. *)
Goal forall (count : bv 64) (k : bv 128),
  ~ bv_signed k < bv_signed (bv_zero_extend 128 count) -> bv_signed k >= bv_unsigned count.
Proof. intros count k H. zesu_exit_fact. Qed.

Goal forall (half : bv 16), bv_zero_extend 64 half = BV 64 0 -> bv_unsigned half = 0.
Proof. intros half H. zesu_exit_fact. Qed.

Goal forall (b : bv 8), 0 <= bv_unsigned b.
Proof. intros b. zesu_exit_fact. Qed.

Goal forall (b : bv 8), bv_unsigned b <= 255.
Proof. intros b. zesu_exit_fact. Qed.

Print Assumptions loop_exit_zero_witnesses.
