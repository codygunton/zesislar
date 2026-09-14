Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier150f8Scratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

Definition writeSuccessTransactions150f8CarrierCallFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col
      (delete 0%nat
        (delete 3%nat
          (delete 3%nat writeSuccessTransactions15028OtherRegShapes))) ∗
   writeSuccessTransactions150f8CarrierScratchRest
     sp base (length transactions) (length processed) transaction
     first second third fourth items ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     writeSuccessTransactionBytes transaction ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
     writeSuccessTransactionsBytes remaining ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessByteArrayOwn (writeSuccessTransactionDataPointer transaction)
     (writeSuccessTransactionData transaction) ∗
   writeSuccessTransactionRestOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
       first second third fourth items) ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactions150f8CarrierCallFrame.

Lemma write_success_transactions_150f8_carrier_call_frame_enter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items -∗
  writeSuccessTransactions150f8CarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
  (bv_unsigned sp - 32) ↦ₘ? 32 ∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
  (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
  ⌜length (writeSuccessTransactionBytes transaction) = 288%nat⌝ ∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
  ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝.
Proof.
  iIntros "Hframe".
  iEval (unfold writeSuccessTransactions150ecCarrierCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(H34 & Hscratch & Harray & Hprefix & Hsuffix & Hprocessed & Hdata &
      Hrest & Hremaining & HP & Hinvariant & Hexit & HloadFacts & _)".
  iPoseProof (write_success_transactions_150f8_carrier_scratch_split
    sp base (length transactions) (length processed) transaction
    first second third fourth items with "Hscratch") as
    "(Hscratch & Hstack & Hvalue & Htag)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "HloadFacts".
  iDestruct "HloadFacts" as
    "(%Hlength & %Halign & %Hlower & %Hupper & %Hspalign & %Hspmin &
      %Hspmax & _)".
  iSplitL "H34 Hscratch Harray Hprefix Hsuffix Hprocessed Hdata Hrest
    Hremaining HP Hinvariant Hexit".
  - rewrite /writeSuccessTransactions150f8CarrierCallFrame
      /writeSuccessTransactionsLoadFacts. iFrame.
    repeat (iSplit; first (iPureIntro; assumption)). done.
  - iFrame. repeat iSplit; iPureIntro; assumption.
Qed.

Lemma write_success_transactions_150f8_carrier_call_frame_exit
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (tag : bv 8) (tagTail : list (bv 8)) :
  writeSuccessTransactions150f8CarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items -∗
  (bv_unsigned sp - 32) ↦ₘ? 32 -∗
  (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 -∗
  (bv_unsigned sp + 1672) ↦ₘ tag -∗
  (bv_unsigned sp + 1673) ↦ₘ∗ tagTail -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned (writeSuccessTransactionWord transaction 168)) =
    tag :: tagTail⌝ -∗
  writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items.
Proof.
  iIntros "Hframe Hstack Hvalue Htag Htail" (Hshape).
  iEval (unfold writeSuccessTransactions150f8CarrierCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(H34 & Hscratch & Harray & Hprefix & Hsuffix & Hprocessed & Hdata &
      Hrest & Hremaining & HP & Hinvariant & Hexit & HloadFacts & _)".
  iPoseProof (write_success_transactions_150f8_carrier_tag_combine sp
    transaction tag tagTail with "Htag Htail []") as "Htagword".
  { iPureIntro. exact Hshape. }
  iEval (unfold writeSuccessTransactions150f8CarrierScratchRest) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower16 & Hupper104 & Hscratch)".
  have HstackAddr : bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32 by lia.
  have HupperAddr : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower16 Hstack Hupper104]" as "Hlower".
  { iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[Hlower16 Hstack]" as "Hlower48".
    { iApply (mem_mapsto_uninit_combine 16 with "[Hlower16] [Hstack]");
        [lia | iExact "Hlower16"
         | iEval (rewrite HstackAddr); iExact "Hstack"]. }
    iApply (mem_mapsto_uninit_combine 48 with "[Hlower48] [Hupper104]");
      [lia | iExact "Hlower48"
       | iEval (rewrite HupperAddr); iExact "Hupper104"]. }
  rewrite /writeSuccessTransactions150ecCarrierCallFrame
    /writeSuccessTransactions150ecCarrierScratch.
  iFrame.
Qed.
