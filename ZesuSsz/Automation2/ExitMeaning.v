Require Import isla.riscv64.riscv64.

Class ZesuExitMeaning {Sigma} (source : iProp Sigma) (facts : Prop) : Prop :=
  zesu_exit_meaning : source ⊢ ⌜facts⌝.
#[global] Hint Mode ZesuExitMeaning + + - : typeclass_instances.

(* This marker retains the exact source, facts, and registered evidence. *)
Inductive ZesuExitMeaningApplied {Sigma} (source : iProp Sigma)
    (facts : Prop) (evidence : ZesuExitMeaning source facts) : Prop :=
  ZesuExitMeaningWasApplied.

Class ZesuStepExitMeaning : Prop := zesu_step_exit_meaning : True.
