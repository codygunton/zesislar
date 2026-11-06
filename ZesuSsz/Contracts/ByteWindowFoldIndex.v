From Coq Require Import Lists.List ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Open Scope Z_scope.

Lemma zesu_byte_window_index_zero (bytes : list (bv 8)) (start : nat) :
  bv_unsigned (BV 64 0) = zesu_byte_window_fold bytes start (Z.to_nat 0).
Proof.
  rewrite zesu_byte_window_zero. reflexivity.
Qed.
