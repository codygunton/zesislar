Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Lemma write_success_blob_hashes_segment15_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessBlobHashesBodySpec P -∗ writeSuccessBlobHashesLbuEntry P.
Proof.
  iIntros "Hentry".
  rewrite /writeSuccessBlobHashesBodySpec.
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hother & Hx2 & Hx19 & Hx27 & Harray & Hscratch & Hmmio &
      Hevents & HP & Hinv & Hexit & _)".
  iPoseProof "Hinv" as "HinvCopy".
  iDestruct "HinvCopy" as
    "(%Htotal & %HlengthTotal & %Hpointer & %HremainingBound &
      %HspAlign & %HspLower & %HspUpper & %HbaseLower & %HbaseUpper & _)".
  have Hlength :
      length bytes = (32 * (processed + S remaining))%nat by
    rewrite Htotal in HlengthTotal; exact HlengthTotal.
  rewrite /writeSuccessBlobHashesLbuEntry.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "Hsys Hother Hx19 Harray".
  rewrite /writeSuccessBlobHashesLbuOuterFrame.
  iFrame "Hx2 Hx27 Hscratch Hmmio Hevents HP".
  rewrite /writeSuccessFixedWidthArrayInvariant.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.
