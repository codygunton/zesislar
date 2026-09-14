Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.

Definition writeSuccessTransactionsLoopCarrierPayload
    `{!islaG Sigma} `{!threadG} (sp first second third fourth : bv 64)
    (items : list ByteListItem) : iProp Sigma :=
  (writeSuccessTransactionsWordsCarrier sp first second third fourth ∗
   (bv_unsigned sp - 80) ↦ₘ? 32 ∗
   byteListItemResources (bv_unsigned first) items ∗
   ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopCarrierPayload) := I.

Definition writeSuccessTransactionsEventScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (first second : bv 64) (items : list ByteListItem)
    : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 984 ∗
   (bv_unsigned sp + 1104) ↦ₘ first ∗
   (bv_unsigned sp + 1112) ↦ₘ second ∗
   (bv_unsigned sp + 1120) ↦ₘ? 776 ∗
   byteListItemResources (bv_unsigned first) items ∗
   ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
   ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsEventScratch) := I.

Lemma write_success_transactions_event_scratch_split
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (first second : bv 64) (items : list ByteListItem) :
  writeSuccessTransactionsEventScratch sp base transactions first second items -∗
  ∃ third fourth,
    writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
    writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48.
Proof.
  iIntros "Hscratch".
  rewrite /writeSuccessTransactionsEventScratch
    /writeSuccessTransactionsPuncturedScratch
    /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier.
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Htotal & Hprefix & Hfirst & Hsecond & Hsuffix &
      Hitems & %Hfacts & Hframe & %Halign16 & %Halign8 & %Hlow & %Hhigh)".
  iDestruct (mem_mapsto_uninit_split 8 with "Hsuffix") as
    "[Hthird Hsuffix]"; first lia.
  have HfourthAddress : bv_unsigned sp + 1120 + 8 =
      bv_unsigned sp + 1128 by lia.
  iEval (rewrite HfourthAddress) in "Hsuffix".
  iDestruct (mem_mapsto_uninit_split 8 with "Hsuffix") as
    "[Hfourth Hsuffix]"; first lia.
  have HsuffixAddress : bv_unsigned sp + 1128 + 8 =
      bv_unsigned sp + 1136 by lia.
  iEval (rewrite HsuffixAddress;
    replace (776 - 8 - 8)%Z with 760%Z by lia) in "Hsuffix".
  iDestruct (mem_mapsto_uninit_split 608 with "Hsuffix") as
    "[Hmiddle Hsuffix]"; first lia.
  have HwithdrawalsAddress : bv_unsigned sp + 1136 + 608 =
      bv_unsigned sp + 1744 by lia.
  iEval (rewrite HwithdrawalsAddress) in "Hsuffix".
  iDestruct (mem_mapsto_uninit_split 48 with "Hsuffix") as
    "[Hwithdrawals Htail]"; first lia.
  have HtailAddress : bv_unsigned sp + 1744 + 48 =
      bv_unsigned sp + 1792 by lia.
  iEval (rewrite HtailAddress;
    replace (760 - 608 - 48)%Z with 104%Z by lia) in "Htail".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hthird") as
    (thirdLength third HthirdLength) "Hthird".
  cbn in HthirdLength. subst thirdLength.
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hfourth") as
    (fourthLength fourth HfourthLength) "Hfourth".
  cbn in HfourthLength. subst fourthLength.
  iExists third, fourth.
  iFrame.
  iPureIntro. exact Hfacts.
Qed.


Lemma write_success_transactions_event_scratch_combine
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (Halign16 : bv_unsigned sp `mod` 16 = 0)
    (Halign8 : bv_unsigned sp `mod` 8 = 0)
    (Hlow : (mapRamBase defaultMap) <= bv_unsigned sp - 48)
    (Hhigh : bv_unsigned sp + 1896 < (machineRamEnd defaultMap)) :
  writeSuccessTransactionsPuncturedScratch sp base (length transactions) -∗
  writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items -∗
  (bv_unsigned sp + 1744) ↦ₘ? 48 -∗
  writeSuccessTransactionsEventScratch sp base transactions first second items.
Proof.
  iIntros "Hscratch Hcarrier Hwithdrawals".
  rewrite /writeSuccessTransactionsEventScratch
    /writeSuccessTransactionsPuncturedScratch
    /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier.
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Htotal & Hprefix & Hmiddle & Htail & _)".
  iDestruct "Hcarrier" as
    "((Hfirst & Hsecond & Hthird & Hfourth) & Hframe & Hitems & %Hfacts)".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hthird") as "Hthird".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hfourth") as "Hfourth".
  iAssert ((bv_unsigned sp + 1136) ↦ₘ? 760)%I
    with "[Hmiddle Hwithdrawals Htail]" as "Hsuffix".
  { iApply (mem_mapsto_uninit_combine 608 with "Hmiddle"); first lia.
    have -> : bv_unsigned sp + 1136 + 608 = bv_unsigned sp + 1744 by lia.
    iApply (mem_mapsto_uninit_combine 48 with "Hwithdrawals"); first lia.
    have -> : bv_unsigned sp + 1744 + 48 = bv_unsigned sp + 1792 by lia.
    iExact "Htail". }
  iAssert ((bv_unsigned sp + 1120) ↦ₘ? 776)%I
    with "[Hthird Hfourth Hsuffix]" as "HsuffixFull".
  { iApply (mem_mapsto_uninit_combine 8 with "Hthird"); first lia.
    have -> : bv_unsigned sp + 1120 + 8 = bv_unsigned sp + 1128 by lia.
    iApply (mem_mapsto_uninit_combine 8 with "Hfourth"); first lia.
    have -> : bv_unsigned sp + 1128 + 8 = bv_unsigned sp + 1136 by lia.
    iExact "Hsuffix". }
  iFrame.
  unfold writeSuccessTransactionsPost15674ByteListFacts in Hfacts.
  destruct Hfacts as
    (Hcount & HitemsBound & HfirstAlign & HfirstLow & HfirstHigh &
      HspExtract & HspLow & HspHigh).
  repeat iSplit; try iPureIntro; try assumption.
Qed.


Definition writeSuccessTransactionsLoopExitEventsFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (tail : spec) (first second : bv 64) (items : list ByteListItem)
    : iProp Sigma :=
  (writeSuccessTransactionsEventScratch sp base transactions first second items ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
     (byteListItemEvents (sp - BV 64 32)%bv items
       (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))) ∗ P)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopExitEventsFrame) := I.

Definition writeSuccessTransactionsLoopExitEvents
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
    (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsLoopExitEventsFrame P sp base transactions tail
     first second items)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopExitEvents) := I.

Definition writeSuccessTransactionsLoopEventsFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (first second : bv 64)
    (items : list ByteListItem) (exit : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionsOwn remaining ∗
   writeSuccessTransactionsEventScratch sp base transactions first second items ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessTransactionsEvents sp remaining
     (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
       (byteListItemEvents (sp - BV 64 32)%bv items
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)))) ∗
   P ∗
   writeSuccessTransactionsInvariant
     sp base transactions processed remaining bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress exit ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopEventsFrame) := I.

Definition writeSuccessTransactionsLoopEventsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem),
    writeSuccessTransactionsLoopEventsFrame P sp base transactions processed
      remaining bytes prefix suffix tail first second items
      (writeSuccessTransactionsLoopExitEvents P sp base transactions bytes tail
        first second items))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopEventsSpec) := I.

Definition writeSuccessTransactionPhaseEventsHandoff
    `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessTransactionPhase) (machine : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (first second : bv 64)
    (items : list ByteListItem) (P : iProp Sigma) : iProp Sigma :=
  (machine ∗ base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗
   writeSuccessTransactionsEventScratch sp base transactions first second items ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeSuccessTransactionPhaseEvents phase sp transaction
       (writeSuccessTransactionsEvents sp remaining
         (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
           (byteListItemEvents (sp - BV 64 32)%bv items
             (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))))) ∗
   P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExitEvents P sp base transactions bytes tail
       first second items) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionPhaseEventsHandoff) := I.

Lemma write_success_transactions_loop_events_pack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (first second : bv 64)
    (items : list ByteListItem) :
  reg_col zesu_ram_sys_regs -∗
  reg_col writeSuccessTransactionsOtherRegShapes -∗
  "x2" ↦ᵣ RVal_Bits sp -∗
  "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) -∗
  "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) -∗
  base ↦ₘ∗ prefix -∗
  (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix -∗
  writeSuccessTransactionsOwn processed -∗
  writeSuccessTransactionsOwn remaining -∗
  writeSuccessTransactionsEventScratch sp base transactions first second items -∗
  mmio_range (machineOutputAddress defaultMap) 16 -∗
  spec_trace (writeSuccessTransactionsEvents sp remaining
    (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)))) -∗
  P -∗
  writeSuccessTransactionsInvariant
    sp base transactions processed remaining bytes prefix suffix -∗
  instr_pre writeSuccessTransactionsLoopExitAddress
    (writeSuccessTransactionsLoopExitEvents P sp base transactions bytes tail
      first second items) -∗
  writeSuccessTransactionsLoopEventsSpec P.
Proof.
  iStartProof.
  iIntros "Hsys Hother H2 H10 H11 Hprefix Hsuffix Hprocessed Hremaining
    Hscratch Hmmio Htrace HP Hinvariant Hexit".
  iExists sp, base, transactions, processed, remaining, bytes, prefix, suffix,
    tail, first, second, items.
  iFrame.
Qed.


Lemma write_success_transaction_phase_events_handoff_pack
    `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessTransactionPhase) (machine : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (first second : bv 64)
    (items : list ByteListItem) (P : iProp Sigma) :
  machine -∗
  base ↦ₘ∗ prefix -∗
  (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix -∗
  writeSuccessTransactionsProcessedOwn processed -∗
  writeSuccessTransactionOwn transaction -∗
  writeSuccessTransactionsOwn remaining -∗
  writeSuccessTransactionsEventScratch sp base transactions first second items -∗
  mmio_range (machineOutputAddress defaultMap) 16 -∗
  spec_trace
    (writeSuccessTransactionPhaseEvents phase sp transaction
      (writeSuccessTransactionsEvents sp remaining
        (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
          (byteListItemEvents (sp - BV 64 32)%bv items
            (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))))) -∗
  P -∗
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  instr_pre writeSuccessTransactionsLoopExitAddress
    (writeSuccessTransactionsLoopExitEvents P sp base transactions bytes tail
      first second items) -∗
  writeSuccessTransactionPhaseEventsHandoff phase machine sp base transaction
    transactions processed remaining bytes prefix suffix tail first second items P.
Proof.
  iStartProof.
  iIntros "Hmachine Hprefix Hsuffix Hprocessed Htransaction Hremaining
    Hscratch Hmmio Htrace HP Hinvariant Hexit".
  iFrame.
Qed.

Definition writeSuccessTransactionsLoopCarrierExit
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
    "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
     (byteListItemEvents (sp - BV 64 32)%bv items
    (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))) ∗ P ∗ True)%I.

(** This event boundary keeps the decoded words at [1120(sp)] and [1128(sp)]
    exact.  The generic event scratch uses an uninitialized region there, but
    the withdrawals continuation needs both values after the event output. *)
Definition writeSuccessTransactionsLoopExitEventsData
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
     (byteListItemEvents (sp - BV 64 32)%bv items
       (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Definition writeSuccessTransactionsLoopExitWithdrawalsData
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (count : nat)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  writeSuccessTransactionsLoopExitEventsData P sp base transactions bytes tail
    first second pointer (Z_to_bv 64 (Z.of_nat count)) items.

Definition writeSuccessTransactionsLoopCarrierFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (exit : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) ∗
   base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionsOwn remaining ∗
   writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessTransactionsEvents sp remaining
     (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
       (byteListItemEvents (sp - BV 64 32)%bv items
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)))) ∗ P ∗
   writeSuccessTransactionsInvariant
     sp base transactions processed remaining bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress exit ∗ True)%I.

Definition writeSuccessTransactionsLoopCarrierSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    writeSuccessTransactionsLoopCarrierFrame P sp base transactions processed
      remaining bytes prefix suffix tail first second third fourth items
      (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
        first second third fourth items))%I.

Definition writeSuccessTransactionPhaseCarrierHandoff
    `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessTransactionPhase) (machine : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (P : iProp Sigma) : iProp Sigma :=
  (machine ∗ base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeSuccessTransactionPhaseEvents phase sp transaction
       (writeSuccessTransactionsEvents sp remaining
         (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
           (byteListItemEvents (sp - BV 64 32)%bv items
             (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))))) ∗
   P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
       first second third fourth items) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopCarrierExit) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopExitEventsData) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopExitWithdrawalsData) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopCarrierFrame) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopCarrierSpec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionPhaseCarrierHandoff) := I.

Lemma write_success_transactions_loop_carrier_exit_to_events_data
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (Halign16 : bv_unsigned sp `mod` 16 = 0)
    (Halign8 : bv_unsigned sp `mod` 8 = 0)
    (Hlow : (mapRamBase defaultMap) <= bv_unsigned sp - 48)
    (Hhigh : bv_unsigned sp + 1896 < (machineRamEnd defaultMap)) :
  writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
    first second third fourth items -∗
  writeSuccessTransactionsLoopExitEventsData P sp base transactions bytes tail
    first second third fourth items.
Proof.
  iIntros "Hexit".
  rewrite /writeSuccessTransactionsLoopCarrierExit
    /writeSuccessTransactionsLoopExitEventsData.
  iDestruct "Hexit" as
    "(Hsys & Hother & H2 & H10 & H11 & Hbytes & Hown & Hscratch &
      Hcarrier & Hwithdrawals & Hmmio & Htrace & HP & _)".
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.

Lemma write_success_transactions_loop_carrier_exit_to_events
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (count : nat)
    (first second : bv 64) (items : list ByteListItem)
    (Halign16 : bv_unsigned sp `mod` 16 = 0)
    (Halign8 : bv_unsigned sp `mod` 8 = 0)
    (Hlow : (mapRamBase defaultMap) <= bv_unsigned sp - 48)
    (Hhigh : bv_unsigned sp + 1896 < (machineRamEnd defaultMap)) :
  writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
    first second pointer (Z_to_bv 64 (Z.of_nat count)) items -∗
  writeSuccessTransactionsLoopExitWithdrawalsData P sp pointer base transactions
    bytes tail count first second items.
Proof.
  iIntros "Hexit".
  rewrite /writeSuccessTransactionsLoopExitWithdrawalsData.
  iApply (write_success_transactions_loop_carrier_exit_to_events_data P
    sp base transactions bytes tail first second pointer
    (Z_to_bv 64 (Z.of_nat count)) items Halign16 Halign8 Hlow Hhigh
    with "Hexit").
Qed.
