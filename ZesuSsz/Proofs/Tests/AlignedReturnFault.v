Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

(* The actual step entry must refute this pure branch before Iris setup. *)
Lemma zesu_aligned_return_fault_entry (returnValue : Z) :
  0 <= returnValue -> returnValue < 18446744073709551616 ->
  returnValue mod 4 = 0 ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 returnValue) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1 ->
  False.
Proof.
  intros Hlower Hupper Haligned Hfault.
  solve [zesu_liAStep].
Qed.

Print Assumptions zesu_aligned_return_fault_entry.
