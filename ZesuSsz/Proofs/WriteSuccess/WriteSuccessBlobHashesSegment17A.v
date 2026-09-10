Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17Prepare.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17Core.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17Return.

Lemma write_success_blob_hashes_segment17_a `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15490 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x1548c (writeSuccessBlobHashesBodySpec P).
Proof.
  iIntros "#Hlookup Hnext".
  rewrite instr_pre'_eq. iIntros "Hbody".
  iPoseProof (write_success_blob_hashes_segment15_entry P with "Hbody")
    as "Hentry".
  iPoseProof (write_success_blob_hashes_segment17_prepare P with "Hentry")
    as "Hprepared".
  iDestruct "Hprepared" as
    (sp pointer base total processed remaining bytes tail byte) "Hstate".
  iAssert (instr_body 0x15490
    (writeSuccessBlobHashesLbuResult P "x21" 18 0 sp pointer base total
      processed remaining bytes tail byte))%I with "[Hnext]" as "Hreturn".
  { rewrite instr_pre'_eq. iIntros "Hresult".
    iPoseProof (write_success_blob_hashes_segment17_return P sp pointer base
      total processed remaining bytes tail byte with "Hresult") as "Hbody".
    iApply "Hnext". iExact "Hbody". }
  iPoseProof (write_success_blob_hashes_segment17_core P sp pointer base total
    processed remaining bytes tail byte with "Hlookup Hreturn") as "Hcore".
  iEval (rewrite instr_pre'_eq) in "Hcore".
  iApply "Hcore". iExact "Hstate".
Qed.
