Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.

Lemma copied_tail_words_owner_preserved `{!islaG Sigma}
    (sp : bv 64) (decodedBytes : list (bv 8)) :
  writeSuccessExactCopiedTailWords sp decodedBytes -∗
  writeSuccessExactCopiedTailWords sp decodedBytes.
Proof.
  iStartProof. iIntros "Hwords".
  iEval (unfold writeSuccessExactCopiedTailWords).
  zesu_open_matching_copied_word_package.
  iFrame "∗".
Qed.
Print Assumptions copied_tail_words_owner_preserved.
