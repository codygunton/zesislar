(* Call-specific ownership rules remain disabled in legacy proofs. *)
Require Import isla.riscv64.riscv64.

Class ZesuStepCallOwnership : Prop := zesu_step_call_ownership : True.

Ltac zesu_call_ownership_on :=
  let enabled := constr:(_ : ZesuStepCallOwnership) in idtac.
