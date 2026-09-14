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
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedHeaderLiveFrame.
Lemma write_success_exact_copied_header_value_live_entry `{!islaG Sigma} `{!threadG}
    sp base transactions transactionBytes sourceBytes object values payload tail (P : iProp Sigma) :
  default (BV 64 0) (take 69 values !! 7%nat) = Z_to_bv 64 base ->
  default (BV 64 0) (take 69 values !! 8%nat) =
    Z_to_bv 64 (Z.of_nat (length transactions)) ->
  writeSuccessExactValuePost sp values payload
    (writeSuccessExactTransactionsEvents sp transactions tail)
    (writeSuccessExactHeaderValueFrame
      (writeSuccessExactCopiedHeaderLiveFrameRest sp base transactions transactionBytes object P)
      sp sourceBytes) -∗
  transactionLiveLoopState sp base transactions [] transactions transactionBytes tail
    (writeSuccessExactCopiedValueLiveCaller sp values payload sourceBytes object
      (writeSuccessNativeStaticResources ∗ P)).
Proof.
  intros Hbase Hcount. iIntros "Hpost".
  iApply (write_success_exact_copied_value_live_entry _ _ _ _ _ _ _ _ _ _ Hbase Hcount).
  rewrite /writeSuccessExactValuePost.
  iDestruct "Hpost" as
    "(Hsys & Hregs & H2 & H10 & H11 & Hlow & Hmemory & Hpayload & Hbase & Hcount & Hmmio & Htrace & Hframe & _)".
  iPoseProof (write_success_exact_copied_header_live_frame with "Hframe") as "HliveFrame".
  iFrame.
Qed.
Print Assumptions write_success_exact_copied_header_value_live_entry.

