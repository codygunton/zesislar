From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Lemma write_success_transactions_carrier_phase_handoff_pack
    `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessTransactionPhase) (machine : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (P : iProp Sigma) :
  machine -∗
  base ↦ₘ∗ prefix -∗
  (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix -∗
  writeSuccessTransactionsProcessedOwn processed -∗
  writeSuccessTransactionOwn transaction -∗
  writeSuccessTransactionsOwn remaining -∗
  writeSuccessTransactionsLoopCarrierPayload
    sp first second third fourth items -∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 -∗
  mmio_range 0x2401a0c0 16 -∗
  spec_trace
    (writeSuccessTransactionPhaseEvents phase sp transaction
      (writeSuccessTransactionsEvents sp remaining
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
          (byteListItemEvents (sp - BV 64 32)%bv items
            (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))))) -∗
  P -∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  instr_pre writeSuccessTransactionsLoopExitAddress
    (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
      first second third fourth items) -∗
  writeSuccessTransactionPhaseCarrierHandoff phase machine sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items P.
Proof.
  iStartProof.
  iIntros "Hmachine Hprefix Hsuffix Hprocessed Htransaction Hremaining
    Hcarrier Hwithdrawals Hmmio Htrace HP Hinvariant Hexit".
  iFrame.
Qed.

Lemma write_success_transactions_carrier_phase_handoff_unpack
    `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessTransactionPhase) (machine : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (P : iProp Sigma) :
  writeSuccessTransactionPhaseCarrierHandoff phase machine sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items P -∗
  machine ∗
  base ↦ₘ∗ prefix ∗
  (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
  writeSuccessTransactionsProcessedOwn processed ∗
  writeSuccessTransactionOwn transaction ∗
  writeSuccessTransactionsOwn remaining ∗
  writeSuccessTransactionsLoopCarrierPayload
    sp first second third fourth items ∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
  mmio_range 0x2401a0c0 16 ∗
  spec_trace
    (writeSuccessTransactionPhaseEvents phase sp transaction
      (writeSuccessTransactionsEvents sp remaining
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
          (byteListItemEvents (sp - BV 64 32)%bv items
            (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))))) ∗
  P ∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix ∗
  instr_pre writeSuccessTransactionsLoopExitAddress
    (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
      first second third fourth items) ∗ True.
Proof.
  iIntros "Hhandoff".
  iEval (unfold writeSuccessTransactionPhaseCarrierHandoff) in "Hhandoff".
  iExact "Hhandoff".
Qed.
