Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15APrepare.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15AReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15ACore.

Lemma write_success_blob_hashes_segment15a `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15460 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x1545c (writeSuccessBlobHashesBodySpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iPoseProof (write_success_blob_hashes_segment15_entry P with "Hentry")
    as "Hentry".
  iPoseProof (write_success_blob_hashes_segment15a_prepare P with "Hentry") as
    (sp pointer base total processed remaining bytes tail byte) "Hstate".
  iAssert (instr_body 0x15460
    (writeSuccessBlobHashesLbuResult P "x18" 16 10 sp pointer base total
      processed remaining bytes tail byte))%I with "[Hnext]" as "Hresult".
  { rewrite instr_pre'_eq. iIntros "Hresult".
    rewrite /writeSuccessBlobHashesLbuResult.
    iDestruct "Hresult" as
      "(Hsys & Hother & Htarget & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
        %HlookupByte & %Hpointer & Houter)".
    iApply "Hnext".
    iApply (write_success_blob_hashes_segment15a_return P sp pointer base total
      processed remaining bytes tail byte with
      "Hsys Hother Htarget Hx19 Hbyte Hdone Hprefix Hsuffix [] [] Houter").
    - iPureIntro. exact HlookupByte.
    - iPureIntro. exact Hpointer. }
  iPoseProof (write_success_blob_hashes_segment15a_core P sp pointer base total
    processed remaining bytes tail byte with "Hlookup Hresult") as "Hcore".
  iEval (rewrite instr_pre'_eq) in "Hcore".
  iApply "Hcore". iExact "Hstate".
Qed.
