Require Import ZesuSsz.Automation2.SwitchDispatch.
From stdpp Require Import bitvector.tactics.
From Coq Require Import ZArith.ZArith.
Local Open Scope Z_scope.

Class ZesuStepWordIdentity : Prop := {}.

(* Only definitional zero images and closed-displacement cast identities enter
   this rule. No hypothesis, decoder registration or machine predicate is added. *)
Ltac zesu_word_identity :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepWordIdentity);
  lazymatch goal with
  | |- @eq (bv ?width) ?lhs (Z_to_bv ?target_width ?value) =>
      constr_eq width target_width;
      is_closed_term width;
      lazymatch lhs with
      | @BV _ Z0 _ =>
          solve [apply bv_eq; change (0%Z = 0%Z); reflexivity]
      | bv_add (Z_to_bv ?source_width ?base) ?offset =>
          constr_eq width source_width;
          lazymatch value with
          | Z.sub ?target_base ?displacement =>
              constr_eq base target_base;
              assert_fails (has_evar base);
              is_closed_term offset;
              is_closed_term displacement;
              let reduced := eval vm_compute in displacement in
              let reduced_offset := eval vm_compute in offset in
              solve [change (bv_add (Z_to_bv width base) reduced_offset =
                             Z_to_bv width (base - reduced)%Z);
                     bv_solve]
          end
      end
  end.
