Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

(* Open separating groups. Keep memory arrays and register collections whole. *)
Ltac zesu_open_resource_groups :=
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
