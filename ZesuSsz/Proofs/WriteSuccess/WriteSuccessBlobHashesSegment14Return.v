Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment14Frame.

Lemma write_success_blob_hashes_segment14_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  writeSuccessBlobHashesLbuResult P "x8" 6 8 sp pointer base total
    processed remaining bytes tail byte -∗
  writeSuccessBlobHashesBodySpec P.
Proof.
  iIntros "Hresult".
  rewrite /writeSuccessBlobHashesLbuResult.
  iDestruct "Hresult" as
    "(Hsys & Hother & Hx8 & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %Hlookup & %Hpointer & Houter)".
  iPoseProof (write_success_blob_hashes_segment15_recombine_lbu pointer
    base processed 8 bytes byte with
    "[] [] Hdone Hbyte Hprefix Hsuffix") as "Harray".
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact Hlookup. }
  iPoseProof (write_success_blob_hashes_segment14_raw_registers byte with
    "Hother Hx8") as "Hother".
  iEval (unfold writeSuccessBlobHashesLbuOuterFrame) in "Houter".
  iDestruct "Houter" as
    "(Hx2 & Hx27 & Hscratch & Hmmio & Hevents & HP & Hinv & Hexit & _)".
  rewrite /writeSuccessBlobHashesBodySpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "Hsys Hother Hx19 Harray Hx2 Hx27 Hscratch Hmmio Hevents HP
    Hinv Hexit".
Qed.
