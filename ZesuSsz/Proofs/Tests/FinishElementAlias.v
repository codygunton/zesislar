Require Import isla.riscv64.riscv64.
Require SailStdpp.MachineWord.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* An index side condition counts elements at `bv (Z_idx 8)`; the range fact
   counts them at `bv 8`. Linear arithmetic alone sees two `length` atoms. *)
Lemma finish_element_alias (lower address : Z)
    (values : list (bv (SailStdpp.MachineWord.MachineWord.Z_idx 8))) :
  (lower <= address < lower + Z.of_nat (@length (bv 8) values))%Z ->
  (Z.to_nat ((address - lower) `div` 1) < @length (bv (SailStdpp.MachineWord.MachineWord.Z_idx 8)) values)%nat.
Proof.
  intros Hrange.
  Fail solve [zesu_linear_goal_shape; zesu_solve_machine_linear].
  ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia.
Qed.

(* The step needs `Z_idx` in the goal. *)
Lemma finish_element_alias_guard (count : nat) :
  (count < count + 1)%nat.
Proof.
  tryif ZesuSsz.Automation2.Hooks.zesu_finish_element_alias then fail else idtac.
  ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia.
Qed.

Print Assumptions finish_element_alias.
