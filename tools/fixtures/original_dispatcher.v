Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.UnionRuleComponents.
Require Import ZesuSsz.Automation.OriginalDispatcher.

(* These test-local branches isolate the two accepted dispatch controls. *)
Module OriginalDispatcherControls.
Ltac zesu_open_nested_existential_packages := fail.
Ltac zesu_codec_array_read := fail.
Ltac zesu_prefer_owned_instr_pre := fail.
Ltac zesu_bundle_dispatcher184 :=
 first [
   liEnsureInvariant;
   try progress (unfold TRACE_LET);
   try liAIntroduceLetInGoal;
   first [progress zesu_open_nested_existential_packages
         | zesu_codec_array_read
         | zesu_prefer_owned_instr_pre]; liSimpl
 | zesu_original_dispatcher184 ].

Ltac liEnsureInvariant ::= idtac.
Ltac liSimpl ::= idtac.
Ltac ZesuSsz.Automation.UnionRuleComponents.zesu_region_fault_if_enabled ::= exact I.
Ltac zesu_liAStep ::= fail 100 "A dynamic original alias was used".
Lemma captured_fallback_ignores_dynamic_alias : True.
Proof. zesu_bundle_dispatcher184. Qed.

Ltac zesu_open_nested_existential_packages ::= exact I.
Ltac ZesuSsz.Automation.OriginalDispatcher.zesu_original_dispatcher184 ::=
  fail 100 "Fallback ran before the new branch".
Lemma new_branch_precedes_fallback : True.
Proof. zesu_bundle_dispatcher184. Qed.
End OriginalDispatcherControls.
