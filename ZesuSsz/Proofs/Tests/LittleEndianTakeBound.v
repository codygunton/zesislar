Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* A byte-window word bound is refused by the rewrite-bound guard
   (Automation2/RewriteBoundGuards.v) before the consumer's solver fallback
   runs: the guard's failure leaves the enclosing `first`. *)
Lemma little_endian_take_bound_no_fallback (bytes : list (bv 8))
    (H : 0 <= little_endian_to_bv 8 (take (N.to_nat 8) bytes) < bv_modulus 64) : True.
Proof.
  Fail assert (0 <= little_endian_to_bv 8 (take (N.to_nat 8) bytes) < bv_modulus 64)
    by (first [ZesuSsz.Automation2.RewriteBoundGuards.a3n_closed_bound_if_enabled | exact H]).
  exact I.
Qed.

(* A closed bound is still proved by the guard. *)
Lemma closed_bound_proved : 0 <= 3 < 5.
Proof. ZesuSsz.Automation2.RewriteBoundGuards.a3n_closed_bound_if_enabled. Qed.

(* Any other goal still reaches the consumer's fallback. *)
Lemma open_bound_falls_back (x y : Z) (H : x <= y) : x <= y.
Proof. first [ZesuSsz.Automation2.RewriteBoundGuards.a3n_closed_bound_if_enabled | exact H]. Qed.
