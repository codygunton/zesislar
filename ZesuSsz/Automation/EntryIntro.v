Require Import isla.riscv64.riscv64.

Class ZesuEntryIntro {Sigma} (source : iProp Sigma) (facts : Prop) : Prop :=
  zesu_entry_intro : source ⊢ ⌜facts⌝.
#[global] Hint Mode ZesuEntryIntro + + - : typeclass_instances.

Class ZesuLoopStep {Sigma} (source : iProp Sigma) (facts : Prop) : Prop :=
  zesu_loop_step : source ⊢ ⌜facts⌝.
#[global] Hint Mode ZesuLoopStep + + - : typeclass_instances.
