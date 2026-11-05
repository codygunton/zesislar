Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Proofs.Tests.BranchGuards.
Require Import isla.riscv64.riscv64.

(* Remove the release instances locally to preserve the isolation refusal. *)
Section ReleaseSwitchIsolation.
#[local] Remove Hints
  ZesuSsz.Automation.All.zesu_union_branch_guards_enabled
  ZesuSsz.Automation.Switches.BranchGuards.zesu_branch_guards_enabled : typeclass_instances.

Lemma branch_guards_import_isolation (word : bv 64) :
  SimplImpl (bv_signed (bv_zero_extend 128 word) < 0) (bv_unsigned word < 0).
Proof.
  Fail zesu_switch_enabled constr:(ZesuSsz.Automation.BitvectorFacts.ZesuStepBranchGuards).
  Fail let marker := constr:(_ : ZesuStepBranchGuards) in idtac.
  Fail zesu_branch_guard_simpl_impl.
  unfold SimplImpl. rewrite zesu_signed_zero_extend_64_128. tauto.
Qed.

Print Assumptions branch_guards_import_isolation.

End ReleaseSwitchIsolation.
Require Import ZesuSsz.Automation.All.
