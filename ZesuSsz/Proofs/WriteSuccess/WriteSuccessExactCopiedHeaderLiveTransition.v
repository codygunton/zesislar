Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedValueLiveEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderValue.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.

Require Import ZesuSsz.Automation.All.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessExactCopiedHeaderValueLiveEntry WriteSuccessExactCopiedHeaderLiveFrame WriteSuccessExactCopiedValueLiveEntry.
Lemma write_success_exact_copied_header_live_transition `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes object values payload tail (P : iProp Sigma) :
  default (BV 64 0) (take 69 values !! 7%nat) = Z_to_bv 64 base ->
  default (BV 64 0) (take 69 values !! 8%nat) =
    Z_to_bv 64 (Z.of_nat (length transactions)) ->
  length values = 74%nat ->
  bytes_of_u64s values = take 592 sourceBytes ->
  bv_unsigned (writeSuccessExactValueWord values 5) = length payload ->
  bv_unsigned sp `mod` 16 = 0 ->
  bv_unsigned sp `mod` 8 = 0 ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 48 ->
  bv_unsigned sp + 1896 < machineRamEnd defaultMap ->
  □ instr_pre 0x14f04
    (transactionLiveLoopState sp base transactions [] transactions transactionBytes tail
      (writeSuccessExactCopiedValueLiveCaller sp values payload sourceBytes object
        (writeSuccessNativeStaticResources ∗ P))) -∗
  (bv_unsigned sp - 48) ↦ₘ? 48 -∗
  bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload -∗
  writeSuccessExactCopiedHeaderLiveFrameRest sp base transactions transactionBytes object P -∗
  writeSuccessExactHeaderValueTransition
    (writeSuccessExactCopiedHeaderLiveFrameRest sp base transactions transactionBytes object P)
    sp sourceBytes values payload (writeSuccessExactTransactionsEvents sp transactions tail).
Proof.
  intros Hbase Hcount Hlength Hbytes Hpayload Halign16 Halign8 Hlower Hupper.
  iIntros "#Hloop Hlow Hpayload Hrest".
  rewrite /writeSuccessExactHeaderValueTransition.
  iFrame. repeat iSplit; try iPureIntro; try assumption.
  iApply (instr_pre_wand 0x14f04 0x14f04 true true with "Hloop");
    [done | reflexivity |].
  iIntros "Hpost".
  iApply (write_success_exact_copied_header_value_live_entry _ _ _ _ _ _ _ _ _ _ Hbase Hcount with "Hpost").
Qed.
Print Assumptions write_success_exact_copied_header_live_transition.
