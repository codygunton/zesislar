(* Arithmetic on wrapped stack addresses. A block's range facts bound a
   stack address (a word plus offsets, wrapped at 2^64) through its 128-bit
   zero extension compared as a signed number:
   `bv_signed (bv_zero_extend 128 (sp + c1 + c2)) >= bv_signed (BV 128 lo)`.
   A goal or a window offset states the same address unwrapped
   (`bv_unsigned sp - 400 + 48`) or wrapped. The facts then fix every wrap:
   unfolded to Z with their constants evaluated, lia proves the goal on the
   range facts alone. Proving it on the whole context, or with bv_solve,
   does not finish (decodeParentHeader 0300). *)
From Coq Require Import ZArith.ZArith micromega.Lia micromega.Zify.
From stdpp.bitvector Require Import definitions tactics.
Require Import ZesuSsz.Automation2.BoundedSolve.
Local Open Scope Z_scope.

Ltac zesu_stack_range_fact T :=
  match T with
  | context [@bv_signed _ ?value] =>
      lazymatch value with context [@bv_zero_extend _ _ (@bv_add _ _ _)] => idtac end
  end.

Ltac zesu_stack_literal value :=
  lazymatch value with Z0 => idtac | Zpos ?p => is_ground p | Zneg ?p => is_ground p end.

Ltac zesu_stack_fold_constants :=
  repeat match goal with
  | H : context [@bv_unsigned ?n (@BV ?m ?z ?p)] |- _ => change (@bv_unsigned n (@BV m z p)) with z in H
  | |- context [@bv_unsigned ?n (@BV ?m ?z ?p)] => change (@bv_unsigned n (@BV m z p)) with z
  end;
  cbn [Z.of_N] in *;
  repeat match goal with
  | H : context [(?a ^ ?k)%Z] |- _ => zesu_stack_literal a; zesu_stack_literal k;
      let v := eval vm_compute in (a ^ k)%Z in change (a ^ k)%Z with v in H
  | |- context [(?a ^ ?k)%Z] => zesu_stack_literal a; zesu_stack_literal k;
      let v := eval vm_compute in (a ^ k)%Z in change (a ^ k)%Z with v
  end;
  repeat match goal with
  | H : context [(?a / ?b)%Z] |- _ => zesu_stack_literal a; zesu_stack_literal b;
      let v := eval vm_compute in (a / b)%Z in change (a / b)%Z with v in H
  | |- context [(?a / ?b)%Z] => zesu_stack_literal a; zesu_stack_literal b;
      let v := eval vm_compute in (a / b)%Z in change (a / b)%Z with v
  end.

(* A Z goal over wrapped address sums, proved from the range facts alone. *)
Ltac zesu_stack_range_lia :=
  lazymatch goal with |- ?g => lazymatch type of g with Prop => idtac end end;
  lazymatch goal with |- context [@bv_unsigned _ (@bv_add _ _ _)] => idtac end;
  match goal with H : ?T |- _ => zesu_stack_range_fact T end;
  repeat match goal with
  | H : ?T |- _ => lazymatch type of T with Prop => idtac end;
      tryif zesu_stack_range_fact T then fail else clear H
  end;
  repeat match goal with
  | H : ?T |- _ => zesu_stack_range_fact T;
      rewrite ?bv_zero_extend_signed, ?bv_add_signed, ?bv_add_unsigned,
        ?bv_zero_extend_signed, ?bv_add_unsigned in H
  end;
  rewrite ?bv_add_unsigned;
  repeat match goal with
  | |- context [@bv_unsigned ?n ?x] =>
      lazymatch x with @BV _ _ _ => fail | @bv_add _ _ _ => fail | _ => idtac end;
      lazymatch goal with _ : (0 <= @bv_unsigned n x < _)%Z |- _ => fail | _ =>
        pose proof (bv_unsigned_in_range n x) end
  end;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *;
  zesu_stack_fold_constants;
  zesu_bounded_lia_on_context.

Ltac zesu_stack_offset_term e :=
  match e with
  | context [@bv_unsigned _ (@bv_add _ ?x _)] =>
      lazymatch x with @BV _ _ _ => fail | _ => idtac end
  end.

(* An offset over one word takes its value at a word far from both wrap
   points; zesu_stack_range_lia proves that value from the range facts. *)
Ltac zesu_stack_offset_rewrite e :=
  match e with
  | context [@bv_unsigned ?n ?x] =>
      lazymatch x with @BV _ _ _ => fail | @bv_add _ _ _ => fail | _ => idtac end;
      lazymatch eval pattern x in e with
      | ?f _ =>
          let v := eval vm_compute in (f (Z_to_bv n (2 ^ (Z.of_N n - 2))%Z)) in
          zesu_stack_literal v;
          let Hc := fresh "Hoffset" in
          assert (Hc : e = v) by zesu_stack_range_lia;
          rewrite Hc; clear Hc
      end
  end.

(* Window offsets (`Z.to_nat e`) over stack addresses, also inside the local
   definitions the goal names, become constants. *)
Ltac zesu_stack_offsets :=
  repeat match goal with
  | x := ?body |- _ =>
      lazymatch goal with |- context [x] => idtac end;
      lazymatch body with context [Z.to_nat ?e] => zesu_stack_offset_term e end;
      unfold x
  end;
  progress (repeat match goal with
  | |- context [Z.to_nat ?e] => zesu_stack_offset_term e; zesu_stack_offset_rewrite e
  end).
