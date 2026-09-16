Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopEntryBody.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopEntryExit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.

Definition writeSuccessTransactionsMachine14f08Carrier
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed : list writeSuccessTransaction) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (Z.of_nat (length processed))) ∗
   writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
   True)%I.

Definition writeSuccessTransactionsAt14f08CarrierSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    writeSuccessTransactionPhaseCarrierHandoff TransactionType
      (writeSuccessTransactionsMachine14f08Carrier
        sp base transactions processed)
      sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items P)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsMachine14f08Carrier) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt14f08CarrierSpec) := I.

Lemma write_success_transactions_loop_carrier_entry_body
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (Hfacts : writeSuccessTransactionsLoopEntryFacts
      sp base processed remaining)
    (Hneq : Z_to_bv 64 (Z.of_nat (length processed)) <>
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) :
  writeSuccessTransactionsLoopCarrierFrame P sp base
      (processed ++ remaining) processed remaining
      (writeSuccessTransactionsBytes (processed ++ remaining))
      (writeSuccessTransactionsBytes processed)
      (writeSuccessTransactionsBytes remaining) tail
      first second third fourth items
      (writeSuccessTransactionsLoopCarrierExit P sp base
        (processed ++ remaining)
        (writeSuccessTransactionsBytes (processed ++ remaining)) tail
        first second third fourth items) -∗
  writeSuccessTransactionsAt14f08CarrierSpec P.
Proof.
  destruct remaining as [|transaction remaining].
  { rewrite app_nil_r in Hneq. contradiction. }
  iIntros "Hframe".
  iEval (unfold writeSuccessTransactionsLoopCarrierFrame) in "Hframe".
  rewrite /writeSuccessTransactionsAt14f08CarrierSpec.
  iDestruct "Hframe" as
    "(Hsys & Hother & H2 & H10 & H11 & Hprefix & Hsuffix & Hprocessed &
      Hremaining & Hscratch & Hcarrier & Hwithdrawals & Hmmio & Htrace & HP & Hinvariant &
      Hexit & _)".
  iDestruct "Hremaining" as "(Htransaction & Hremaining & _)".
  iExists sp, base, transaction, (processed ++ transaction :: remaining),
    processed, remaining,
    (writeSuccessTransactionsBytes (processed ++ transaction :: remaining)),
    (writeSuccessTransactionsBytes processed),
    (writeSuccessTransactionsBytes (transaction :: remaining)), tail,
    first, second, third, fourth, items.
  rewrite /writeSuccessTransactionPhaseCarrierHandoff
    /writeSuccessTransactionsMachine14f08Carrier.
  iFrame "Hsys Hother H2 H10 H11 Hscratch Hwithdrawals Hprefix Hsuffix
    Htransaction Hremaining Hcarrier Hmmio Htrace HP Hexit".
  iSplitL "Hprocessed".
  { rewrite /writeSuccessTransactionsProcessedOwn. iExact "Hprocessed". }
  rewrite /writeSuccessTransactionsInvariant
    /writeSuccessTransactionsLoopEntryFacts in Hfacts.
  destruct Hfacts as
    (Hbytes & Hlength & HprefixLength & HsuffixLength & Hbound & HspAlign &
      HspLow & HspHigh & HbaseAlign & HbaseLow & HbaseHigh).
  repeat iSplit; try iPureIntro; try assumption; try reflexivity.
Qed.

Definition writeSuccessTransactionsLoopCarrierExitBranchFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
    iProp Sigma :=
  ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionsBytes remaining ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionsOwn remaining ∗
   writeSuccessTransactionsPuncturedScratch sp base
     (length (processed ++ remaining)) ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessTransactionsEvents sp remaining
     (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
       (byteListItemEvents (sp - BV 64 32)%bv items
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)))) ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopCarrierExitBranchFrame) := I.

Lemma write_success_transactions_loop_carrier_entry_exit
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (Hbound : (length (processed ++ remaining) < 2 ^ 64)%nat)
    (Heq : Z_to_bv 64 (Z.of_nat (length processed)) =
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) :
  writeSuccessTransactionsLoopCarrierExitBranchFrame P sp base processed
      remaining tail first second third fourth items -∗
  writeSuccessTransactionsOwn (processed ++ remaining) ∗
  writeSuccessTransactionsPuncturedScratch sp base
    (length (processed ++ remaining)) ∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
  mmio_range (machineOutputAddress defaultMap) 16 ∗
  spec_trace (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
    (byteListItemEvents (sp - BV 64 32)%bv items
      (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))) ∗ P ∗ True.
Proof.
  iIntros "Hframe".
  have Hnil := write_success_transactions_loop_exit_remaining_nil
    processed remaining Hbound Heq.
  subst remaining. rewrite app_nil_r.
  iEval (unfold writeSuccessTransactionsLoopCarrierExitBranchFrame) in "Hframe".
  iDestruct "Hframe" as
    "(_ & Hprocessed & _ & Hscratch & Hcarrier & Hwithdrawals & Hmmio & Htail & HP & _)".
  iEval (rewrite app_nil_r) in "Hscratch".
  iFrame.
Qed.
