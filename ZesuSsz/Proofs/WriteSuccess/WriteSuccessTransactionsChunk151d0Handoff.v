Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0Helpers.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0HandoffEmpty.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151d0HandoffNonempty.

Lemma write_success_transactions_151d0_access_handoff
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8))
    (tail phase : spec) (P : iProp Sigma)
    (HaccessBounds :
      forall (transaction :
          WriteSuccessTransactionsSpec.writeSuccessTransaction),
        WriteSuccessTransactionsSpec.writeSuccessTransactionValid transaction ->
        (0x20000000 <= bv_unsigned
           (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer
              transaction))%Z /\
        (bv_unsigned
           (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer
              transaction) +
         Z.of_nat
           (length
             (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessBytes
                transaction)) < 0x40000000)%Z) :
  (∀ (sp : bv 64) (base : Z)
      (entries : list writeSuccessAccessEntry)
      (bytes : list (bv 8)) (tail : spec) (x19 savedX22 : bv 64),
    instr_body 0x153c0
      (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P)) -∗
  "x22" ↦ᵣ RVal_Bits
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) -∗
  "x27" ↦ᵣ RVal_Bits
    (bv_zero_extend 64
      (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)) -∗
  (bv_unsigned sp - 48) ↦ₘ? 152 -∗
  (bv_unsigned sp + 136) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 -∗
  (bv_unsigned sp + 256) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208 -∗
  (bv_unsigned sp + 264) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216 -∗
  (bv_unsigned sp + 272) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 -∗
  (bv_unsigned sp + 1680) ↦ₘ? 64 -∗
  (bv_unsigned sp + 1744) ↦ₘ? 40 -∗
  base ↦ₘ∗ prefix -∗
  (base + 288 * length processed) ↦ₘ∗ suffix -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionsOwn remaining -∗
  mmio_range 604086464 16 -∗
  spec_trace
    (writeSuccessAccessListsEvents sp
      (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
        transaction) phase) -∗
  P -∗
  WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant sp base
    transactions processed (transaction :: remaining) bytes prefix suffix -∗
  instr_pre
    WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExitAddress
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExit
      sp base transactions bytes tail P) -∗
  write_success_transactions_151d0_post sp transaction P.
Proof.
  iIntros "HexitBody Hx22 Hx27 Hlower Hm136 Hm256 Hm264 Hm272 Hstorage HtoScratch Hbase Hsuffix Hprocessed Htransaction Hremaining Hmmio Htrace HP Hinv Hexit".
  destruct (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries
    transaction) as [|entry entries] eqn:Hentries.
  - iEval (rewrite <- Hentries) in "Htrace".
    iApply (write_success_transactions_151d0_access_handoff_empty
      sp base transaction transactions processed remaining bytes prefix suffix tail phase P HaccessBounds Hentries with
      "HexitBody Hx22 Hx27 Hlower Hm136 Hm256 Hm264 Hm272 Hstorage HtoScratch Hbase Hsuffix Hprocessed Htransaction Hremaining Hmmio Htrace HP Hinv Hexit").
  - iEval (rewrite <- Hentries) in "Htrace".
    iApply (write_success_transactions_151d0_access_handoff_nonempty
      sp base transaction transactions processed remaining bytes prefix suffix tail phase P HaccessBounds entry entries Hentries with
      "HexitBody Hx22 Hx27 Hlower Hm136 Hm256 Hm264 Hm272 Hstorage HtoScratch Hbase Hsuffix Hprocessed Htransaction Hremaining Hmmio Htrace HP Hinv Hexit").
Qed.
