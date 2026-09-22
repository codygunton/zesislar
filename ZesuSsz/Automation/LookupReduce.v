(* C7: the instruction the lookup holds, in the form the search reads.

   A segment carries its code as `instr_lookup_resources lookup`, and
   the search finds an instruction there as `instr address (lookup
   address)`. Islaris can turn that into the `instr_pre` a returning
   call needs -- `subsume_instr_some_pre` does exactly that -- but the
   instance wants `instr address (Some trace)`, and `lookup address` is
   an application, not a constructor.

   So the search stalls on `subsume (instr a (lookup a)) (fun _ =>
   instr_pre a …)` with the answer one reduction away. This computes the
   lookup at a literal address and puts the result in the goal. It is
   guarded twice: the address has to reduce to a literal, and the lookup
   has to reduce to `Some`. A symbolic address fails the first guard
   before anything expensive runs.

   Measured on tail fields 1: with this step the block runs on past its
   first returning call instead of stopping there. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
From iris.proofmode Require Import environments.
From Coq Require Import ZArith.ZArith.

Ltac zesu_reduce_instr_lookup :=
  lazymatch goal with
  | |- envs_entails _ (subsume (instr ?address ?code) _ _) =>
      lazymatch code with
      | Some _ => fail
      | _ =>
          let literal := eval vm_compute in address in
          lazymatch literal with
          | Z0 => idtac
          | Zpos _ => idtac
          | Zneg _ => idtac
          end;
          let reduced := eval vm_compute in code in
          lazymatch reduced with
          | Some _ => change code with reduced
          end
      end
  end.

(* The switch for this one rule. `Automation/Switch.v` provides it
   with every other v2 step; `Automation/Switches/…` provides it
   alone, which is how one benchmark arm measures one rule. *)
Class ZesuStepLookupReduce : Prop := zesu_step_lookup_reduce : True.

Ltac zesu_step_lookup_reduce_on :=
  let _ := constr:(_ : ZesuStepLookupReduce) in idtac.

Ltac zesu_reduce_instr_lookup_if_enabled :=
  zesu_step_lookup_reduce_on; zesu_reduce_instr_lookup.
