From stdpp Require Import bitvector.definitions.
From Coq Require Import ZArith Lia.
Local Open Scope Z_scope.

(* A branch condition can exist only as a bit-vector (dis)equality, `E = b` or
   `E <> b`, while the goal states it over `bv_unsigned E`. lia and bv_solve
   read no bv-typed hypothesis, so this closer restates one hypothesis about E
   over `bv_unsigned`, reduces a constant side, and closes the goal from that
   fact alone. Clearing the rest keeps the solver call small: the full context
   can hold hundreds of facts. *)

Ltac zesu_bv_unsigned_close_from H :=
  let Hz := fresh "Hbv_unsigned" in
  lazymatch type of H with
  | @eq (bv ?n) ?a ?b => pose proof (proj1 (bv_eq n a b) H) as Hz
  | not (@eq (bv ?n) ?a ?b) => pose proof (proj1 (bv_neq n a b) H) as Hz
  end;
  cbn [bv_unsigned] in Hz;
  clear - Hz; Lia.lia.

Ltac zesu_bv_hypothesis_unsigned :=
  lazymatch goal with
  | |- @eq Z (bv_unsigned ?E) _ => idtac
  | |- @eq Z _ (bv_unsigned ?E) => idtac
  | |- not (@eq Z (bv_unsigned ?E) _) => idtac
  | |- not (@eq Z _ (bv_unsigned ?E)) => idtac
  end;
  let E := lazymatch goal with
    | |- @eq Z (bv_unsigned ?E) _ => E
    | |- @eq Z _ (bv_unsigned ?E) => E
    | |- not (@eq Z (bv_unsigned ?E) _) => E
    | |- not (@eq Z _ (bv_unsigned ?E)) => E
    end in
  match goal with
  | H : @eq (bv _) E _ |- _ => solve [zesu_bv_unsigned_close_from H]
  | H : @eq (bv _) _ E |- _ => solve [zesu_bv_unsigned_close_from H]
  | H : not (@eq (bv _) E _) |- _ => solve [zesu_bv_unsigned_close_from H]
  | H : not (@eq (bv _) _ E) |- _ => solve [zesu_bv_unsigned_close_from H]
  end.
