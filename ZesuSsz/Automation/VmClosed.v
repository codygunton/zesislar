From stdpp Require Import tactics.

(* Local definitions can hide unresolved evars from the outer term. *)
Ltac zesu_vm_has_unresolved term :=
  first [has_evar term |
    multimatch goal with
    | local := ?body : _ |- _ =>
        lazymatch term with
        | context[local] => zesu_vm_has_unresolved body
        end
    end].

Ltac zesu_vm_closed term :=
  assert_fails ltac:(zesu_vm_has_unresolved term);
  is_closed_term term.
