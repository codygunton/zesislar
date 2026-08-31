Require Import isla.riscv64.riscv64.
Require Export InstrSpecs.Machine.
Require Export ZesuSsz.Contracts.Machine.

Ltac solve_instruction_path solve_edge :=
  lazymatch goal with
  | |- InstructionPathFollows _ (_ :: _ :: _) =>
      apply InstructionPathNext;
      [ solve [solve_edge] | solve_instruction_path solve_edge ]
  | |- InstructionPathFollows _ [_] => constructor
  end.
