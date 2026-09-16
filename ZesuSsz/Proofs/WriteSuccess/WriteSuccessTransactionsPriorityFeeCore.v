Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15118.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15148.

Definition writeSuccessTransactionsPriorityFeeFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions bytes tail P) ∗
   True)%I.

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeFrame.

Definition writeSuccessTransactionsPriorityFeePostSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15148
      sp base transactions processed transaction ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗
    writeSuccessTransactionsPriorityFeeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeePostSpec) := I.

Definition writeSuccessTransactionsPriorityFeeNoneCoreSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15118
      sp base transactions processed transaction ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
          (writeSuccessTransactionsEvents sp remaining tail))) ∗
    writeSuccessTransactionsPriorityFeeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeNoneCoreSpec) := I.

Definition writeSuccessTransactionsPriorityFeeSomeCoreSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15118
      sp base transactions processed transaction ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 32)%bv (BV 64 16)
          (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
            (writeSuccessTransactionsEvents sp remaining tail)))) ∗
    writeSuccessTransactionsPriorityFeeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeSomeCoreSpec) := I.

Lemma write_success_transactions_priority_fee_post_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsPriorityFeePostSpec P -∗
  writeSuccessTransactionsAt15148Spec P.
Proof.
  iIntros "(%sp & %base & %transaction & %transactions & %processed &
    %remaining & %bytes & %prefix & %suffix & %tail & Hmachine & Hmmio &
    Htrace & Hframe & _)".
  iEval (unfold writeSuccessTransactionsPriorityFeeFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP &
      Hinvariant & Hexit & _)".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactionPhaseHandoff
    /writeSuccessTransactionsProcessedOwn.
  iFrame.
Qed.

Lemma write_success_transactions_priority_fee_none_entry_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsPriorityFeeNoneAt1513cSpec P -∗
  writeSuccessTransactionsPriorityFeeNoneCoreSpec P.
Proof.
  iIntros "(%sp & %base & %transaction & %transactions & %processed &
    %remaining & %bytes & %prefix & %suffix & %tail & %HbyteZero & Hphase)".
  iEval (unfold writeSuccessTransactionPhaseHandoff) in "Hphase".
  iDestruct "Hphase" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  iEval (unfold writeSuccessTransactionOwn) in "Htransaction".
  iDestruct "Htransaction" as
    "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
  destruct (writeSuccessTransactionGasPriorityFee transaction)
    as [[word0 word1] |] eqn:Hpriority.
  { exfalso.
    unfold writeSuccessTransactionValid in Hvalid.
    destruct Hvalid as
      [Hlen [Htype [Hchain [Hnonce [Hgas [HpriorityValid HvalidRest]]]]]].
    rewrite Hpriority in HpriorityValid.
    exact ((proj1 HpriorityValid) HbyteZero). }
  iAssert (writeSuccessTransactionOwn transaction)
    with "[Hdata Haccess Hentries Hblob Hauth]" as "Htransaction".
  { rewrite /writeSuccessTransactionOwn. iFrame; done. }
  iEval (unfold writeSuccessTransactionsProcessedOwn) in "Hprocessed".
  iEval (rewrite /writeSuccessTransactionPhaseEvents /= Hpriority /=)
    in "Htrace".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "Hmachine Hmmio Htrace".
  iEval (unfold writeSuccessTransactionsPriorityFeeFrame).
  iFrame.
Qed.

Lemma write_success_transactions_priority_fee_some_entry_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsPriorityFeeSomeAt1511cSpec P -∗
  writeSuccessTransactionsPriorityFeeSomeCoreSpec P.
Proof.
  iIntros "(%sp & %base & %transaction & %transactions & %processed &
    %remaining & %bytes & %prefix & %suffix & %tail & %HbyteNonzero & Hphase)".
  iEval (unfold writeSuccessTransactionPhaseHandoff) in "Hphase".
  iDestruct "Hphase" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  iEval (unfold writeSuccessTransactionOwn) in "Htransaction".
  iDestruct "Htransaction" as
    "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
  destruct (writeSuccessTransactionGasPriorityFee transaction)
    as [[word0 word1] |] eqn:Hpriority.
  2: {
    exfalso.
    unfold writeSuccessTransactionValid in Hvalid.
    destruct Hvalid as
      [Hlen [Htype [Hchain [Hnonce [Hgas [HpriorityValid HvalidRest]]]]]].
    rewrite Hpriority in HpriorityValid.
    exact (HbyteNonzero HpriorityValid). }
  iAssert (writeSuccessTransactionOwn transaction)
    with "[Hdata Haccess Hentries Hblob Hauth]" as "Htransaction".
  { rewrite /writeSuccessTransactionOwn. iFrame; done. }
  iEval (unfold writeSuccessTransactionsProcessedOwn) in "Hprocessed".
  iEval (rewrite /writeSuccessTransactionPhaseEvents /= Hpriority /=)
    in "Htrace".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "Hmachine Hmmio Htrace".
  iEval (unfold writeSuccessTransactionsPriorityFeeFrame).
  iFrame.
Qed.
