Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.

Definition writeSuccessTransactions15168Frame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsOwn remaining ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
       WriteSuccessTransactionsSpec.TransactionTo sp transaction
       (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
         sp remaining tail)) ∗
   P ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant
     sp base transactions processed (transaction :: remaining) bytes prefix suffix ∗
   instr_pre WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExitAddress
     (WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExit
       sp base transactions bytes tail P) ∗ True)%I.

Lemma write_success_transactions_chunk_15168_pack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 285
    ≠ BV 8 0⌝ -∗
  writeSuccessTransactionsMachine15168 sp base transactions processed transaction -∗
  writeSuccessTransactions15168Frame P sp base transaction transactions processed
    remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsOptionalAddressSomeAt15168Spec P.
Proof.
  iIntros "Hnonzero Hmachine Hframe".
  iExists sp, base, transaction, transactions, processed, remaining, bytes, prefix,
    suffix, tail.
  iSplitL "Hnonzero". { iExact "Hnonzero". }
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff).
  iFrame.
Qed.
