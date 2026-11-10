Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A block loads byte 0 of an owned array and branches on its sign. The
   successor entry states the branch facts on `nth 0 bytes d`; the context
   holds the lookup `bytes !! 0 = Some v` and the facts on v. The source-fact
   closer rewrites the read to v and proves the facts. *)
Lemma array_byte_nth_sign_fact (bytes : list (bv 8)) (p : Z) (v : bv 8) :
  bytes !! Z.to_nat ((p - p) `div` 1) = Some v ->
  ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 v)) < bv_signed (BV 128 0) ->
  ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 (nth 0 bytes (BV 8 0)))) <
    bv_signed (BV 128 0).
Proof.
  intros Hlookup Hsign.
  ZesuSsz.Automation2.SourceFactMatching.zesu_source_fact.
Qed.

Lemma array_byte_nth_strict_bound (bytes : list (bv 8)) (p : Z) (v : bv 8) :
  bytes !! Z.to_nat ((p - p) `div` 1) = Some v ->
  ~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 v)) < bv_signed (BV 128 0) ->
  128 > bv_unsigned (nth 0 bytes (BV 8 0)).
Proof.
  intros Hlookup Hsign.
  ZesuSsz.Automation2.SourceFactMatching.zesu_source_fact.
Qed.

Print Assumptions array_byte_nth_sign_fact.
Print Assumptions array_byte_nth_strict_bound.
