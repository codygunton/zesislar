From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation.ByteWindowFold.
Require Import ZesuSsz.Automation.ByteWindowFoldIndex.
Open Scope Z_scope.

Fixpoint zesu_byte_window_iterate64 (bytes : list (bv 8)) (start count : nat) : bv 64 :=
  match count with
  | O => BV 64 0
  | S previous => bv_or (bv_shiftl (zesu_byte_window_iterate64 bytes start previous) (BV 64 8))
      (bv_zero_extend 64 (List.nth (start + previous)%nat bytes (BV 8 0)))
  end.

Lemma zesu_byte_window_iterate_zero (bytes : list (bv 8)) (start : nat) :
  zesu_byte_window_iterate64 bytes start 0 = BV 64 0.
Proof. reflexivity. Qed.

Lemma zesu_byte_window_iterate_step (bytes : list (bv 8)) (start count : nat) :
  zesu_byte_window_iterate64 bytes start (S count) =
  bv_or (bv_shiftl (zesu_byte_window_iterate64 bytes start count) (BV 64 8))
    (bv_zero_extend 64 (List.nth (start + count)%nat bytes (BV 8 0))).
Proof. reflexivity. Qed.

Lemma zesu_byte_window_iterate_unsigned (bytes : list (bv 8)) (start count : nat) :
  (count <= 8)%nat -> (start + count <= List.length bytes)%nat ->
  bv_unsigned (zesu_byte_window_iterate64 bytes start count) =
    zesu_byte_window_fold bytes start count.
Proof.
  induction count as [|count IH]; intros Hwidth Hlength.
  { rewrite zesu_byte_window_zero. reflexivity. }
  { pose proof (IH ltac:(lia) ltac:(lia)) as Hacc.
    assert (HaccZ : bv_unsigned (zesu_byte_window_iterate64 bytes start count) =
      zesu_byte_window_fold bytes start (Z.to_nat (Z.of_nat count))).
    { rewrite Nat2Z.id. exact Hacc. }
    assert (Hlookup : nth_error bytes (start + Z.to_nat (Z.of_nat count))%nat =
      Some (List.nth (start + count)%nat bytes (BV 8 0))).
    { rewrite Nat2Z.id. apply nth_error_nth'. lia. }
    pose proof (zesu_byte_window_index_step bytes start (Z.of_nat count) (Z.of_nat (S count))
      (zesu_byte_window_iterate64 bytes start count) (List.nth (start + count)%nat bytes (BV 8 0))
      ltac:(lia) ltac:(lia) ltac:(lia) HaccZ Hlookup) as Hstep.
    replace (Z.of_nat count + 1) with (Z.of_nat (S count)) in Hstep by lia.
    rewrite Nat2Z.id in Hstep. exact Hstep. }
Qed.
