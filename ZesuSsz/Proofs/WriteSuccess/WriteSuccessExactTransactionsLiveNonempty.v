Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.

Lemma transactions_live_state_nonempty `{!islaG Sigma} `{!threadG}
    sp base transactions processed remaining bytes tail (P : iProp Sigma) :
  transactionLiveLoopState sp base transactions processed remaining bytes tail P -∗
  ⌜Z_to_bv 64 (Z.of_nat (length processed)) <> Z_to_bv 64 (Z.of_nat (length transactions))⌝ -∗
  transactionLiveLoopState sp base transactions processed remaining bytes tail P ∗
  ⌜remaining <> []⌝ ∗ True.
Proof.
  iStartProof. iIntros "Hstate %Hcursor".
  iDestruct "Hstate" as "(Hsys & Hregs & Hsp & H10 & H11 & Hbytes & Hown & Hscratch & Hmmio & Htrace & %Hfacts & HP & _)".
  have Hrelation := proj1 Hfacts.
  have Hremaining : remaining <> [].
  { intros ->. rewrite app_nil_r in Hrelation. subst transactions.
    apply Hcursor. reflexivity. }
  rewrite /transactionLiveLoopState. iFrame. done.
Qed.
Print Assumptions transactions_live_state_nonempty.
