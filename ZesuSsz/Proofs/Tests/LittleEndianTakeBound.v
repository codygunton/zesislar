Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* A word read from a byte window is in range whatever the bytes are. The
   rewrite-bound guard (Automation2/RewriteBoundGuards.v) proves it from the
   window width, without a fact in the context. *)
Lemma little_endian_take_word_in_range (bytes : list (bv 8)) :
  0 <= little_endian_to_bv 8 (take (N.to_nat 8) bytes) < bv_modulus 64.
Proof. ZesuSsz.Automation2.RewriteBoundGuards.a3n_closed_bound_if_enabled. Qed.

(* A window wider than the target is not in range in general. *)
Lemma little_endian_take_wide_window_refused (bytes : list (bv 8)) : True.
Proof.
  Fail assert (0 <= little_endian_to_bv 8 (take 9 bytes) < bv_modulus 64)
    by ZesuSsz.Automation2.RewriteBoundGuards.a3n_closed_bound_if_enabled.
  exact I.
Qed.

(* The normalizer's conditional rewrite now fires on such a word, so the
   wrapped form does not reach later side conditions. *)
Lemma little_endian_take_word_unwrapped (bytes : list (bv 8)) (value : Z) :
  value = little_endian_to_bv 8 (take (N.to_nat 8) bytes) ->
  bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) bytes))) = value.
Proof.
  intros ->. autorewrite with isla_coq_rewrite.
  lazymatch goal with
  | |- little_endian_to_bv 8 (take (N.to_nat 8) bytes) = _ => reflexivity
  end.
Qed.
