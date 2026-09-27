Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.V2Steps.
Require Import isla.riscv64.riscv64.

Lemma test_return_wand_v1_inactive `{!islaG Sigma} `{!threadG}
    (R K : iProp Sigma) :
  (R -∗ K) -∗ ((R -∗ K) ∗ True).
Proof.
  iIntros "Hcontinue".
  tryif zesu_rule_set_v2_on
  then fail "the return-wand definition enabled v2"
  else idtac.
  tryif zesu_rule_set_v2_steps
  then fail "the return-wand step ran without its switch"
  else idtac.
  iSplit; [iExact "Hcontinue" | done].
Qed.
Print Assumptions test_return_wand_v1_inactive.
