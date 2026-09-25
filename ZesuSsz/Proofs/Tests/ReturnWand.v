Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ReturnWand.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

(* A named continuation: the step unfolds it one delta step. *)
Definition zesu_test_return_continuation `{!islaG Sigma} `{!threadG}
    (n : nat) : iProp Sigma := ∃ m : nat, ⌜m = n⌝.

Lemma test_return_wand_named `{!islaG Sigma} `{!threadG} (R : iProp Sigma) :
  (R -∗ zesu_test_return_continuation 3) -∗
  ((R -∗ zesu_test_return_continuation 3) ∗ True).
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  lazymatch goal with
  | |- envs_entails _ (∃ m : nat, ⌜m = 3%nat⌝)%I => idtac
  | |- _ => fail "the continuation was not unfolded"
  end.
  iExists 3%nat. done.
Qed.
Print Assumptions test_return_wand_named.

(* Two wands and a load-table entry: the entry is left to Lithium. *)
Lemma test_return_wand_table_entry `{!islaG Sigma} `{!threadG}
    (R S : iProp Sigma) :
  (R -∗ S -∗ zesu_ld_spec 88304 "x10" "x2" 936) -∗
  ((R -∗ S -∗ zesu_ld_spec 88304 "x10" "x2" 936) ∗ True).
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  lazymatch goal with
  | |- envs_entails _ (zesu_ld_spec _ _ _ _) => idtac
  | |- _ => fail "the table entry was unfolded"
  end.
  iApply ("Hcontinue" with "[$] [$]").
Qed.
Print Assumptions test_return_wand_table_entry.
