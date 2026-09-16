Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoadHeader.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Definition writeSuccessNativeCarrierEvents
    (sp : bv 64) (transactions : list writeSuccessTransaction)
    (items : list ByteListItem) (tail : spec) : spec :=
  writeSuccessTransactionsEvents sp transactions
    (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))).

(** This native-only load remainder preserves the byte-list call frame and
    the exact transaction witnesses for the event-aware carrier. *)
Definition writeSuccessNativeEventRemainder
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
  (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) (items : list ByteListItem)
    (withdrawalsBase : bv 64) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (postData : WriteSuccessPostTransactionData) :
    iProp Sigma :=
  (reg_col writeSuccessLoadHeaderExtraRegisters ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp - 80) ↦ₘ? 32 ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
   base ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsInvariant sp base transactions [] transactions
     transactionBytes [] transactionBytes ∗
   ⌜length sourceBytes = 720%nat⌝ ∗
   ⌜bytes_of_u64s values = take 592 sourceBytes⌝ ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
   ⌜writeSuccessValueWord values 7 = Z_to_bv 64 base⌝ ∗
   ⌜writeSuccessValueWord values 8 =
      Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9)) items ∗
   bv_unsigned withdrawalsBase ↦ₘ∗ withdrawalsBytes ∗
   ⌜writeSuccessTransactionsPost15674ByteListFacts sp
      (writeSuccessValueWord values 9) (writeSuccessValueWord values 10)
      items⌝ ∗
   ⌜writeSuccessValueWord values 11 = withdrawalsBase⌝ ∗
   ⌜writeSuccessValueWord values 12 =
      Z_to_bv 64 (Z.of_nat withdrawalsCount)⌝ ∗
   ⌜length withdrawalsBytes = (48 * withdrawalsCount)%nat⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned withdrawalsBase⌝ ∗
   ⌜bv_unsigned withdrawalsBase + Z.of_nat (length withdrawalsBytes) <
      (machineRamEnd defaultMap)⌝ ∗
   writeSuccessPostTransactionDataResources sp sourceBytes decodedBytes
     postData ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessNativeEventRemainder) := I.

Lemma write_success_native_carrier_payload_pack
    `{!islaG Sigma} `{!threadG}
    (sp first second withdrawalsBase : bv 64) (items : list ByteListItem)
    (withdrawalsBytes : list (bv 8)) (withdrawalsCount : nat) :
  writeSuccessTransactionsWordsCarrier sp first second withdrawalsBase
    (Z_to_bv 64 (Z.of_nat withdrawalsCount)) -∗
  (bv_unsigned sp - 80) ↦ₘ? 32 -∗
  byteListItemResources (bv_unsigned first) items -∗
  ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ -∗
  bv_unsigned withdrawalsBase ↦ₘ∗ withdrawalsBytes -∗
  ⌜length withdrawalsBytes = (48 * withdrawalsCount)%nat⌝ -∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned withdrawalsBase⌝ -∗
  ⌜bv_unsigned withdrawalsBase + Z.of_nat (length withdrawalsBytes) <
    (machineRamEnd defaultMap)⌝ -∗
  writeSuccessTransactionsLoopCarrierPayload sp first second withdrawalsBase
    (Z_to_bv 64 (Z.of_nat withdrawalsCount)) items ∗
  bv_unsigned withdrawalsBase ↦ₘ∗ withdrawalsBytes ∗
  ⌜length withdrawalsBytes = (48 * withdrawalsCount)%nat⌝ ∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned withdrawalsBase⌝ ∗
  ⌜bv_unsigned withdrawalsBase + Z.of_nat (length withdrawalsBytes) <
    (machineRamEnd defaultMap)⌝.
Proof.
  iIntros "Hwords Hcall Hitems Hfacts Hbytes Hlength Hmin Hmax".
  rewrite /writeSuccessTransactionsLoopCarrierPayload.
  iFrame.
Qed.

Lemma write_success_native_event_remainder_pack
    `{!islaG Sigma} `{!threadG} {Decoded} (P : iProp Sigma)
    (witness : writeSuccessNativeWitness Decoded) :
  reg_col writeSuccessLoadHeaderExtraRegisters -∗
  writeSuccessNativeDataResources witness -∗
  P -∗
  writeSuccessNativeEventRemainder (writeSuccessNativeStaticResources ∗ P)
    (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness)
    (writeSuccessDecodedBytes witness)
    (writeSuccessValues witness) (writeSuccessPayload witness)
    (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
    (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
    (writeSuccessRawTransactions witness)
    (writeSuccessWithdrawalsBase witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness).
Proof.
  iIntros "Hextra Hdata HP".
  iEval (rewrite /writeSuccessNativeDataResources) in "Hdata".
  iDestruct "Hdata" as
    "(Hheap & Hitems & Hwithdrawals & %Hfacts & %HwithdrawalBase &
      %HwithdrawalCount & %HwithdrawalLength & %HwithdrawalMin &
      %HwithdrawalMax & Hpost & Hstatic)".
  iEval (rewrite /writeSuccessLoadHeaderHeapResources) in "Hheap".
  iDestruct "Hheap" as
    "(Hlower & Hcall & Hpayload & Harray & Hown & Hinvariant &
      %HsourceLength & %HvaluesBytes & %HvaluesLength & %HpayloadLength &
      %HbaseEq & %HcountEq & %Halign16 & %Halign8 & %HlowerBound &
      %HupperBound & _)".
  rewrite /writeSuccessNativeEventRemainder.
  iFrame.
  repeat (iSplit; first (iPureIntro; assumption)).
  iPureIntro. assumption.
Qed.
