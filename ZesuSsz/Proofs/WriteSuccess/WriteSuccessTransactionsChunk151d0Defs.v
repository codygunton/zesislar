Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
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
Lemma write_success_transactions_151d0_invariant_facts
    `{!islaG Sigma} (sp : bv 64) (base : Z)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) :
  WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant
    sp base transactions processed remaining
      bytes prefix suffix -∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝.
Proof.
  iIntros "Hinv".
  iPoseProof "Hinv" as "Hfacts".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "Hfacts".
  iDestruct "Hfacts" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %HspAlign & %HspLower &
      %HspUpper & _)".
  repeat iSplit; iPureIntro; try assumption; lia.
Qed.

Definition write_success_transactions_151d0_next
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∀ x19, instr_body 0x151d4 (writeSuccessAccessListsLoopSpec x19 P))%I.

Global Typeclasses Opaque write_success_transactions_151d0_next.

Definition write_success_transactions_151d0_post
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (phase : spec) (x27 x22 savedX22 storedIndex : bv 64)
      (suffixBytes prefixBytes bytes : list (bv 8))
      (processed remaining entries : list writeSuccessAccessEntry)
      (base : Z),
    ⌜0%bv = Z_to_bv 64 (length remaining)⌝ ∗
    "x22" ↦ᵣ RVal_Bits x22 ∗
    "x27" ↦ᵣ RVal_Bits x27 ∗
    base ↦ₘ∗ prefixBytes ∗
    (base + 40 * length remaining) ↦ₘ∗ suffixBytes ∗
    writeSuccessAccessEntriesOwn remaining ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessListsScratch sp base
      (length entries) storedIndex
      savedX22 ∗
    mmio_range 604086464 16 ∗
    spec_trace (writeSuccessAccessListsEvents sp processed phase) ∗ P ∗
    writeSuccessAccessListsInvariant sp base entries remaining processed
      bytes prefixBytes suffixBytes ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit sp base entries bytes phase
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
        savedX22
        P) ∗ True)%I.
