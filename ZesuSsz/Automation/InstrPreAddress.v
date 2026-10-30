(* Prefer an available contract after reducing a concrete target address. *)
Require Import isla.isla.
Require Import ZesuSsz.Automation.VmClosed.
From Coq Require Import ZArith.ZArith.

Class ZesuStepInstrPreAddress : Prop := zesu_step_instr_pre_address : True.

Ltac zesu_instr_pre_literal_positive value :=
  lazymatch value with
  | xH => idtac
  | xO ?rest => zesu_instr_pre_literal_positive rest
  | xI ?rest => zesu_instr_pre_literal_positive rest
  end.

Ltac zesu_reduce_instr_pre_address :=
  lazymatch goal with
  | |- FindInContext (FindInstrKind ?address ?later) FICSyntactic =>
      let _ := constr:(_ : ZesuStepInstrPreAddress) in
      let reduced := eval vm_compute in address in
      lazymatch reduced with
      | Z0 => idtac
      | Zpos ?value => zesu_instr_pre_literal_positive value
      | Zneg ?value => zesu_instr_pre_literal_positive value
      end;
      first [constr_eq address reduced; fail 1
            | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
              typeclasses eauto]
  end.

Global Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  zesu_vm_closed address;
  zesu_reduce_instr_pre_address : typeclass_instances.
