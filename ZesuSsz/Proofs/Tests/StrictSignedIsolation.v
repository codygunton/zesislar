Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Proofs.Tests.StrictSigned.

Lemma strict_signed_import_isolation (x y : bv 64)
    (Hlt : bv_unsigned x < bv_unsigned y) :
  bv_signed (bv_zero_extend 128 x) < bv_signed (bv_zero_extend 128 y).
Proof.
  Fail let marker := constr:(_ : ZesuStepStrictSigned) in idtac.
  Fail zesu_strict_signed_if_enabled.
  exact (zesu_unsigned_lt_signed_zero_extend_64_128 x y Hlt).
Qed.
