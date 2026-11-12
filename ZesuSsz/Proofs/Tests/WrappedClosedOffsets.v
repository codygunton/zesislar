From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The refusal checks below are `Fail` checks; these make sure the names
   they use exist, so they cannot pass for a missing name. *)
Check ZesuSsz.Automation2.WrappedWord.zesu_wrapped_offset_small.
Check ZesuSsz.Automation2.WrappedWord.zesu_wrapped_offset_step.

(* A stack store `sd ra,56(sp)` after `addi sp,sp,-64`: before any lookup
   rule runs, the closed offsets reduce to one literal. The address is
   `base - 8`, not `base + (bv_unsigned _ + bv_unsigned _ - bv_modulus 64)`. *)
Lemma wrapped_closed_two_offsets `{!islaG Sigma} `{!threadG} (base : Z) (value : bv 64) :
  64 <= base < bv_modulus 64 ->
  (base - 8) ↦ₘ value -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + 18446744073709551552 + 56)))
    (fun _ => True%I).
Proof.
  intros Hrange. iIntros "Hword".
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_closed_address_step.
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      constr_eq address (base - 8)
  end.
  liStep. done.
Qed.

(* A byte store `sb a3,-40(s0)` with `s0 = sp - 64 + 64`: three closed
   offsets on one cast. *)
Lemma wrapped_closed_three_offsets `{!islaG Sigma} `{!threadG} (base : Z) (value : bv 8) :
  64 <= base < bv_modulus 64 ->
  (base - 40) ↦ₘ value -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned
      (Z_to_bv 64 base + 18446744073709551552 + 64 + 18446744073709551576)))
    (fun _ => True%I).
Proof.
  intros Hrange. iIntros "Hword".
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_closed_address_step.
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      constr_eq address (base - 40)
  end.
  liStep. done.
Qed.

(* A positive closed sum keeps the `base + k` form. *)
Lemma wrapped_closed_positive_offset `{!islaG Sigma} `{!threadG} (base : Z) (value : bv 64) :
  0 <= base < bv_modulus 64 - 64 ->
  (base + 24) ↦ₘ value -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + 16 + 8)))
    (fun _ => True%I).
Proof.
  intros Hrange. iIntros "Hword".
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_closed_address_step.
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      constr_eq address (base + 24)
  end.
  liStep. done.
Qed.

(* A symbolic offset is refused before VM evaluation. *)
Lemma wrapped_closed_symbolic_refusal (base : Z) (offset : bv 64) : True.
Proof.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_wrapped_closed_chain
    constr:((Z_to_bv 64 base + offset + 8 + 16)%bv).
  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_closed_chain
    constr:((Z_to_bv 64 base + 8 + 8 + 16)%bv).
  exact I.
Qed.

(* One offset is not a chain: other rules own that address form. *)
Lemma wrapped_closed_single_offset_refusal (base : Z) : True.
Proof.
  Fail ZesuSsz.Automation2.WrappedWord.zesu_wrapped_closed_chain
    constr:((Z_to_bv 64 base + 8)%bv).
  exact I.
Qed.

Print Assumptions wrapped_closed_two_offsets.
Print Assumptions wrapped_closed_three_offsets.
Print Assumptions wrapped_closed_positive_offset.
