From Coq Require Import List ZArith.
Require Import isla.isla.

(* First-match lookup for a generated instruction map. The selected trace
   generator checks that each instruction address occurs once. *)
Fixpoint selectedCodeLookup (instructions : list (Z * isla_trace))
    (address : Z) : option isla_trace :=
  match instructions with
  | [] => None
  | (pc, trace) :: rest =>
      if Z.eqb address pc then Some trace else selectedCodeLookup rest address
  end.
