Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueLiveEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderValue.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.

Definition writeSuccessExactHeaderLiveFrameRest `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned sp ↦ₘ? 104 ∗ (bv_unsigned sp + 120) ↦ₘ? 192 ∗
   base ↦ₘ∗ transactionBytes ∗ writeSuccessTransactionsOwn transactions ∗
   ⌜transactionLoopSourceFacts sp base transactions [] transactions transactionBytes⌝ ∗ P)%I.
Global Instance : LithiumUnfold (@writeSuccessExactHeaderLiveFrameRest) := I.

Lemma write_success_exact_header_live_frame `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes (P : iProp Sigma) :
  writeSuccessExactHeaderValueFrame
    (writeSuccessExactHeaderLiveFrameRest sp base transactions transactionBytes P)
    sp sourceBytes -∗
  writeSuccessExactValueLiveFrame sp base transactions transactionBytes sourceBytes
    (writeSuccessNativeStaticResources ∗ P).
Proof.
  rewrite /writeSuccessExactHeaderValueFrame /writeSuccessExactHeaderLiveFrameRest
    /writeSuccessExactValueLiveFrame.
  iIntros "(Hsource & Hhigh & Hstatic & Hlow & Hmiddle & Hbytes & Hown & Hfacts & HP)".
  iFrame.
Qed.
Print Assumptions write_success_exact_header_live_frame.

Lemma write_success_exact_header_value_live_entry `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes values payload tail (P : iProp Sigma) :
  default (BV 64 0) (take 69 values !! 7%nat) = Z_to_bv 64 base ->
  default (BV 64 0) (take 69 values !! 8%nat) =
    Z_to_bv 64 (Z.of_nat (length transactions)) ->
  writeSuccessExactValuePost sp values payload
    (writeSuccessExactTransactionsEvents sp transactions tail)
    (writeSuccessExactHeaderValueFrame
      (writeSuccessExactHeaderLiveFrameRest sp base transactions transactionBytes P)
      sp sourceBytes) -∗
  transactionLiveLoopState sp base transactions [] transactions transactionBytes tail
    (writeSuccessExactValueLiveCaller sp values payload sourceBytes
      (writeSuccessNativeStaticResources ∗ P)).
Proof.
  intros Hbase Hcount. iIntros "Hpost".
  iApply (write_success_exact_value_live_entry _ _ _ _ _ _ _ _ _ Hbase Hcount).
  rewrite /writeSuccessExactValuePost.
  iDestruct "Hpost" as
    "(Hsys & Hregs & H2 & H10 & H11 & Hlow & Hmemory & Hpayload & Hbase & Hcount & Hmmio & Htrace & Hframe & _)".
  iPoseProof (write_success_exact_header_live_frame with "Hframe") as "HliveFrame".
  iFrame.
Qed.
Print Assumptions write_success_exact_header_value_live_entry.

Lemma write_success_exact_header_live_transition `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes values payload tail (P : iProp Sigma) :
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
      (writeSuccessExactValueLiveCaller sp values payload sourceBytes
        (writeSuccessNativeStaticResources ∗ P))) -∗
  (bv_unsigned sp - 48) ↦ₘ? 48 -∗
  bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload -∗
  writeSuccessExactHeaderLiveFrameRest sp base transactions transactionBytes P -∗
  writeSuccessExactHeaderValueTransition
    (writeSuccessExactHeaderLiveFrameRest sp base transactions transactionBytes P)
    sp sourceBytes values payload (writeSuccessExactTransactionsEvents sp transactions tail).
Proof.
  intros Hbase Hcount Hlength Hbytes Hpayload Halign16 Halign8 Hlower Hupper.
  iIntros "#Hloop Hlow Hpayload Hrest".
  rewrite /writeSuccessExactHeaderValueTransition.
  iFrame. repeat iSplit; try iPureIntro; try assumption.
  iApply (instr_pre_wand 0x14f04 0x14f04 true true with "Hloop");
    [done | reflexivity |].
  iIntros "Hpost".
  iApply (write_success_exact_header_value_live_entry _ _ _ _ _ _ _ _ _ Hbase Hcount with "Hpost").
Qed.
Print Assumptions write_success_exact_header_live_transition.
