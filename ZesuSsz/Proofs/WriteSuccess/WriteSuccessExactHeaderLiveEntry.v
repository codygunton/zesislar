Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
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
