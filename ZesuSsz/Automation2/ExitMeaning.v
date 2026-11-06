Require ZesuSsz.Automation.ExitMeaning.
Require Import isla.riscv64.riscv64.

#[global] Hint Mode ZesuSsz.Automation.ExitMeaning.ZesuExitMeaning + + - : typeclass_instances.

(* This marker retains the exact source, facts, and registered evidence. *)
Inductive ZesuExitMeaningApplied {Sigma} (source : iProp Sigma)
    (facts : Prop) (evidence : ZesuSsz.Automation.ExitMeaning.ZesuExitMeaning source facts) : Prop :=
  ZesuExitMeaningWasApplied.

Class ZesuStepExitMeaning : Prop := zesu_step_exit_meaning : True.
