From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsSemanticAdapter
    `{!islaG Sigma} `{!threadG} (entry P : iProp Sigma) : iProp Sigma :=
  (entry -∗ writeSuccessTransactionsLoopSpec P)%I.

Lemma write_success_transactions_semantic_adapter_pre
    `{!islaG Sigma} `{!threadG} (entry P : iProp Sigma) :
  □ writeSuccessTransactionsSemanticAdapter entry P -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  □ instr_pre 0x14f04 entry.
Proof.
  iStartProof. iIntros "#Hadapter #Hloop".
  iModIntro.
  iApply (instr_pre_wand 0x14f04 0x14f04 true true with "Hloop");
    [done | reflexivity |].
  iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsSemanticAdapter) in "Hadapter".
  iApply "Hadapter". iExact "Hentry".
Qed.
