Require Import isla.riscv64.riscv64.

Class ZesuExitMeaning {Sigma} (source : iProp Sigma) (facts : Prop) : Prop :=
  zesu_exit_meaning : source ⊢ ⌜facts⌝.
#[global] Hint Mode ZesuExitMeaning + + - : typeclass_instances.
