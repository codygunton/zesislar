Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma exact_transaction_word_image_16 (base : Z)
    (transaction : writeSuccessTransaction) :
  RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (base + 16 - base))
      (writeSuccessTransactionBytes transaction))))) =
  RVal_Bits (writeSuccessTransactionWord transaction 16).
Proof. zesu_finish. Qed.
Print Assumptions exact_transaction_word_image_16.

Lemma exact_transaction_word_image_24 (base : Z)
    (transaction : writeSuccessTransaction) :
  RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8
    (take 8 (drop (Z.to_nat (base + 24 - base))
      (writeSuccessTransactionBytes transaction))))) =
  RVal_Bits (writeSuccessTransactionWord transaction 24).
Proof. zesu_run. Qed.
Print Assumptions exact_transaction_word_image_24.
