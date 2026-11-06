From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.

Ltac zesu_hypothesis_cast_range_fact width value :=
  change (0 <= value < bv_modulus width)%Z;
  first [assumption | split; assumption].
