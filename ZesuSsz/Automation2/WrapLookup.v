(* Wrap-to-linear at a failed memory lookup (W1b, last resort).

   A lookup at bv_unsigned (Z_to_bv n x + k), with k closed, fails when the
   region it must find is stated at x + c or at bv_unsigned (Z_to_bv n x) + c:
   the solvers cannot show that the sum does not wrap. With c the centered
   residue of bv_unsigned k modulo 2^n, the address equals x + c as soon as
   0 <= x + c < 2^n.

   The pass tries this step last, only when every other step failed. It
   proves that range once, by one linear call on the facts linked to x and
   to the address (the quotient equation of the address is added inside that
   proof only); when the call fails it saturates the derived facts inside the
   same proof and calls once more. It then rewrites the address, and
   bv_unsigned (Z_to_bv n x) when its own range follows, to linear terms in
   the lookup goal (its target and its resources, after the environment
   alias is exposed), and lets the pass retry the lookup. Nothing stays in
   the main context, and the step fails when it proves no equation. *)
From Coq Require Import ZArith Lia.
From Coq Require Import micromega.Zify.
From stdpp Require Import bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.BvLinear.
Require Import ZesuSsz.Automation2.LinearFirstLia.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.StoreMemoryLookup.
Require Import ZesuSsz.Automation2.ResourceGroups.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

Definition zesu_wrap_lookup_centered (modulus value : Z) : Z :=
  if modulus <? 2 * (value mod modulus) then value mod modulus - modulus
  else value mod modulus.

Lemma zesu_wrap_lookup_mod (n : N) (x c : Z) (k : bv n) :
  (bv_unsigned k - c) mod bv_modulus n = 0 ->
  bv_unsigned (bv_add (Z_to_bv n x) k) = (x + c) mod bv_modulus n.
Proof.
  intros Hk. pose proof (bv_modulus_pos n) as Hpos.
  assert (Hne : bv_modulus n <> 0) by lia.
  rewrite bv_add_unsigned. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l.
  replace (x + bv_unsigned k) with (x + c + (bv_unsigned k - c)) by ring.
  rewrite Zplus_mod. rewrite Hk. rewrite Z.add_0_r. apply (Z.mod_mod _ _ Hne).
Qed.

Lemma zesu_wrap_lookup_add (n : N) (x c : Z) (k : bv n) :
  (bv_unsigned k - c) mod bv_modulus n = 0 ->
  0 <= x + c < bv_modulus n ->
  bv_unsigned (bv_add (Z_to_bv n x) k) = x + c.
Proof.
  intros Hk Hrange. rewrite (zesu_wrap_lookup_mod n x c k Hk).
  apply Z.mod_small. exact Hrange.
Qed.

Lemma zesu_wrap_lookup_add_quotient (n : N) (x c : Z) (k : bv n) :
  (bv_unsigned k - c) mod bv_modulus n = 0 ->
  exists quotient, bv_unsigned (bv_add (Z_to_bv n x) k) = x + c - bv_modulus n * quotient.
Proof.
  intros Hk. pose proof (bv_modulus_pos n) as Hpos.
  rewrite (zesu_wrap_lookup_mod n x c k Hk).
  exists ((x + c) / bv_modulus n). apply Z.mod_eq. lia.
Qed.

Lemma zesu_wrap_lookup_cast (n : N) (x : Z) :
  0 <= x < bv_modulus n -> bv_unsigned (Z_to_bv n x) = x.
Proof. intros Hrange. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hrange. Qed.

(* One linear call on the facts linked to the goal. *)
Ltac zesu_wrap_lookup_linear :=
  zesu_bv_modulus_value;
  try (once ltac2:(zesu_linear_clear_unrelated ()));
  zesu_zify_prefix; Zify.zify_saturate; xlia Lia.zchecker.

(* The range, from the facts as they are, else once more after saturating
   the derived facts. Both calls run inside the range proof. *)
Ltac zesu_wrap_lookup_range :=
  first [solve [zesu_wrap_lookup_linear]
        | progress zesu_saturate_derived_facts; solve [zesu_wrap_lookup_linear]].

(* x + c with a negative c written as x - |c|; equal by conversion. *)
Ltac zesu_wrap_lookup_sum x c :=
  lazymatch c with
  | Z0 => x
  | Zneg ?p => constr:(Z.sub x (Zpos p))
  | _ => constr:(Z.add x c)
  end.

Ltac zesu_wrap_lookup_rewrite_cast n x :=
  lazymatch goal with
  | |- context [@bv_unsigned n (Z_to_bv n x)] =>
      let Hcast := fresh "HwrapLookupCast" in
      assert (Hcast : @bv_unsigned n (Z_to_bv n x) = x) by
        (apply zesu_wrap_lookup_cast;
         pose proof (bv_unsigned_in_range n (Z_to_bv n x));
         zesu_wrap_lookup_range);
      rewrite Hcast; clear Hcast
  end.

Ltac zesu_wrap_lookup_retry :=
  zesu_store_lookup_goal;
  zesu_switch_enabled constr:(ZesuStepStoreMemoryLookup);
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      match address with
      | context [@bv_unsigned ?n (bv_add (Z_to_bv ?n ?x) ?k)] =>
          assert_fails (has_evar x);
          tryif is_closed_term x then fail else idtac;
          zesu_vm_closed k;
          let c := zesu_vm_eval_closed
            (zesu_wrap_lookup_centered (bv_modulus n) (bv_unsigned k)) in
          let sum := zesu_wrap_lookup_sum x c in
          let Hsum := fresh "HwrapLookup" in
          assert (Hsum : @bv_unsigned n (bv_add (Z_to_bv n x) k) = sum) by
            (refine (zesu_wrap_lookup_add n x c k ltac:(zesu_vm_closed_decide) _);
             let quotient := fresh "wrapQuotient" in
             let Hquotient := fresh "HwrapQuotient" in
             destruct (zesu_wrap_lookup_add_quotient n x c k ltac:(zesu_vm_closed_decide))
               as [quotient Hquotient];
             pose proof (bv_unsigned_in_range n (bv_add (Z_to_bv n x) k));
             zesu_wrap_lookup_range);
          rewrite Hsum; clear Hsum;
          try zesu_wrap_lookup_rewrite_cast n x
      end
  end.
