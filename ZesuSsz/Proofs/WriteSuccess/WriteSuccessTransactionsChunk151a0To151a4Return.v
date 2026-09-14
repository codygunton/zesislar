Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.

Definition writeSuccessTransactions151a4Outer
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff
    WriteSuccessTransactionsSpec.TransactionValue True
    sp base transaction transactions processed remaining
    bytes prefix suffix tail P.

Global Instance : LithiumUnfold (@writeSuccessTransactions151a4Outer) := I.

Lemma write_success_transactions_chunk_151a0_to_151a4_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  ⌜bv_extract 0 3 (sp + 128) = 0%bv⌝ -∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned (sp + 128)⌝ -∗
  ⌜bv_unsigned (sp + 128) <= machineRamEnd defaultMap - 8⌝ -∗
  writeSuccessTransactionsMachine151a4
    sp base transactions processed transaction -∗
  writeSuccessTransactions151a4Outer P sp base transaction transactions
    processed remaining bytes prefix suffix tail -∗
  ∃ x : spec *ₗ
      list (bv 8) *ₗ list (bv 8) *ₗ list (bv 8) *ₗ
      list WriteSuccessTransactionsSpec.writeSuccessTransaction *ₗ
      list WriteSuccessTransactionsSpec.writeSuccessTransaction *ₗ
      list WriteSuccessTransactionsSpec.writeSuccessTransaction *ₗ
      WriteSuccessTransactionsSpec.writeSuccessTransaction *ₗ
      Z *ₗ bv 64 *ₗ (),
    ⌜bv_extract 0 3 (x.nextₗ.9ₗ + 128) = 0%bv⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned (x.nextₗ.9ₗ + 128)⌝ ∗
    ⌜bv_unsigned (x.nextₗ.9ₗ + 128) <= machineRamEnd defaultMap - 8⌝ ∗
    WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff
      WriteSuccessTransactionsSpec.TransactionValue
      (writeSuccessTransactionsMachine151a4
        x.nextₗ.9ₗ x.9ₗ x.7ₗ x.6ₗ x.8ₗ)
      x.nextₗ.9ₗ x.9ₗ x.8ₗ x.7ₗ x.6ₗ x.5ₗ
      x.4ₗ x.3ₗ x.2ₗ x.1ₗ P.
Proof.
  iIntros (Halign Hmin Hmax) "Hmachine Houter".
  iEval (unfold writeSuccessTransactions151a4Outer,
    WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff) in
    "Houter".
  iDestruct "Houter" as
    "(_ & HbasePrefix & HbaseSuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
    transaction, base, sp, tt)ₗ.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
  iFrame "Hmachine HbasePrefix HbaseSuffix Hprocessed Htransaction Hremaining
    Hmmio Htrace HP Hinvariant Hexit".
Qed.
