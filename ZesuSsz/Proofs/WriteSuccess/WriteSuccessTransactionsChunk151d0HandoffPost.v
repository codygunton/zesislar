Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Defs.

Lemma write_success_transactions_151d0_nonempty_post
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (phase : spec) (P : iProp Sigma)
    (entry : writeSuccessAccessEntry) (entries : list writeSuccessAccessEntry)
    (HaccessCount :
      bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216) =
      Z.of_nat (length (entry :: entries))) :
  "x22" ↦ᵣ RVal_Bits
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) -∗
  "x27" ↦ᵣ RVal_Bits
    (bv_zero_extend 64
      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)) -∗
  (bv_unsigned
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
      ↦ₘ∗ ([] : list (bv 8)) -∗
  (bv_unsigned
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
      ↦ₘ∗ writeSuccessAccessEntriesBytes (entry :: entries) -∗
  writeSuccessAccessEntriesOwn (entry :: entries) -∗
  (bv_unsigned sp + 136) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 -∗
  (bv_unsigned sp + 256) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208 -∗
  (bv_unsigned sp + 264) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216 -∗
  (bv_unsigned sp + 272) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 -∗
  (bv_unsigned sp + 1744) ↦ₘ? 40 -∗
  (bv_unsigned sp - 16) ↦ₘ? 16 -∗
  writeSuccessStorageKeysScratch sp -∗
  mmio_range 604086464 16 -∗
  spec_trace (writeSuccessAccessListsEvents sp (entry :: entries) phase) -∗
  P -∗
  writeSuccessAccessListsInvariant sp
    (bv_unsigned
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
    (entry :: entries) [] (entry :: entries)
    (writeSuccessAccessEntriesBytes (entry :: entries)) []
    (writeSuccessAccessEntriesBytes (entry :: entries)) -∗
  instr_pre 0x153c0
    (writeSuccessAccessListsLoopExit sp
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208))
      (entry :: entries) (writeSuccessAccessEntriesBytes (entry :: entries)) phase
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232)
      P) -∗
  write_success_transactions_151d0_post sp transaction P.
Proof.
  iIntros
    "Hx22 Hx27 HemptyAccess HaccessArray HaccessEntries Hm136 Hm256 Hm264
      Hm272 HtoScratch Hstack16 HstorageScratch Hmmio Htrace HP
      HaccessInvariant HexitAccess".
  iEval (unfold write_success_transactions_151d0_post).
  iExists phase,
    (bv_zero_extend 64
      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176),
    (writeSuccessAccessEntriesBytes (entry :: entries)), [],
    (writeSuccessAccessEntriesBytes (entry :: entries)),
    (entry :: entries), [], (entry :: entries),
    (bv_unsigned
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208)).
  iSplit; first (iPureIntro; bv_solve).
  iSplitL "Hx22"; first iExact "Hx22".
  iSplitL "Hx27"; first iExact "Hx27".
  iSplitL "HemptyAccess"; first iExact "HemptyAccess".
  rewrite Z.add_0_r.
  iSplitL "HaccessArray"; first iExact "HaccessArray".
  iSplit; first done.
  iSplitL "HaccessEntries"; first iExact "HaccessEntries".
  iSplitL "Hm136 Hm256 Hm264 Hm272 HtoScratch Hstack16 HstorageScratch".
  { rewrite /writeSuccessAccessListsScratch.
    have Hm256Eq :
        Z_to_bv 64
          (bv_unsigned
            (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
              transaction 208)) =
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208
      by bv_solve.
    have Hm264Eq :
        Z_to_bv 64 (Z.of_nat (length (entry :: entries))) =
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216.
    { rewrite <- HaccessCount. apply Z_to_bv_bv_unsigned. }
    iEval (rewrite <- Hm256Eq) in "Hm256".
    iEval (rewrite <- Hm264Eq) in "Hm264".
    iFrame. }
  iFrame.
  Unshelve.
  all: try done.
Qed.
