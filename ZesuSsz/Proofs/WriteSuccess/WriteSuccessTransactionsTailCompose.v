Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsTailHelpers.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsTailMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsTailInvariant.

Import ListNotations.

Lemma write_success_transactions_tail_compose
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (nextCount sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  ⌜nextCount =
    Z_to_bv 64 (Z.of_nat (length (processed ++ [transaction])))⌝ -∗
  writeSuccessTransactionsScratch15620
    sp base transactions processed transaction -∗
  base ↦ₘ∗ prefix -∗
  (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix -∗
  writeSuccessTransactionsProcessedOwn processed -∗
  writeSuccessTransactionOwn transaction -∗
  writeSuccessTransactionsOwn remaining -∗
  mmio_range 0x2401a0c0 16 -∗
  spec_trace (writeSuccessTransactionsEvents sp remaining tail) -∗
  P -∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  instr_pre writeSuccessTransactionsLoopExitAddress
    (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) -∗
  ∃ x : spec *ₗ
      list (bv 8) *ₗ list (bv 8) *ₗ list (bv 8) *ₗ
      list writeSuccessTransaction *ₗ list writeSuccessTransaction *ₗ Z *ₗ (),
    ⌜nextCount = Z_to_bv 64 (Z.of_nat (length x.6ₗ))⌝ ∗
    x.7ₗ ↦ₘ∗ x.3ₗ ∗
    (x.7ₗ + 288 * Z.of_nat (length x.6ₗ)) ↦ₘ∗ x.2ₗ ∗
    writeSuccessTransactionsOwn x.6ₗ ∗
    writeSuccessTransactionsOwn x.5ₗ ∗
    writeSuccessTransactionsScratch sp x.7ₗ (length transactions) ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessTransactionsEvents sp x.5ₗ x.1ₗ) ∗ P ∗
    writeSuccessTransactionsInvariant sp x.7ₗ transactions x.6ₗ x.5ₗ
      x.4ₗ x.3ₗ x.2ₗ ∗
    instr_pre writeSuccessTransactionsLoopExitAddress
      (writeSuccessTransactionsLoopExit sp x.7ₗ transactions x.4ₗ
        x.1ₗ P) ∗ True.
Proof.
  iIntros (Hnext) "Hscratch HbasePrefix HbaseSuffix HprocessedOwn
    HtransactionOwn HremainingOwn Hmmio Htrace HP #Hinv Hexit".
  iDestruct "HtransactionOwn" as
    "(Hdata & Haccess & Hentries & Hblob & Hauthorization &
      %HtransactionValid & _)".
  have HtransactionLength :
      length (writeSuccessTransactionBytes transaction) = 288%nat :=
    proj1 HtransactionValid.
  iAssert (writeSuccessTransactionOwn transaction)%I
    with "[Hdata Haccess Hentries Hblob Hauthorization]" as "HtransactionOwn".
  { rewrite /writeSuccessTransactionOwn. iFrame. done. }
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn)
    in "HprocessedOwn".
  iPoseProof (writeSuccessTransactionsOwn_snoc processed transaction with
    "HprocessedOwn HtransactionOwn") as "HprocessedNew".
  iPoseProof "Hinv" as "#HinvCopy".
  iDestruct "HinvCopy" as
    "(_ & _ & %HprefixEq & %HsuffixEq & _ & _ & %HprefixLength & _)".
  iPoseProof (write_success_transactions_memory_snoc base transaction
    processed remaining prefix suffix with
    "[] [] [] [] HbasePrefix HbaseSuffix") as
    "[HbasePrefixNew HremainingBytes]".
  { iPureIntro. exact HprefixEq. }
  { iPureIntro. exact HsuffixEq. }
  { iPureIntro. exact HprefixLength. }
  { iPureIntro. exact HtransactionLength. }
  iPoseProof (write_success_transactions_scratch_15620_to_loop
    sp base transactions processed transaction with "Hscratch")
    as "HscratchNew".
  iPoseProof (write_success_transactions_invariant_snoc
    sp base transaction transactions processed remaining bytes prefix suffix
    with "[] Hinv") as "HinvNew".
  { iPureIntro. exact HtransactionLength. }
  iExists (tail, (writeSuccessTransactionsBytes remaining),
    (writeSuccessTransactionsBytes (processed ++ [transaction])), bytes,
    remaining, (processed ++ [transaction]), base, tt)ₗ.
  cbn.
  iSplit; [done |].
  iFrame.
  done.
Qed.
