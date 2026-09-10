Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17Prepare90.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17Core90.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment17Return90.

Lemma write_success_blob_hashes_segment17_b `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15490 (writeSuccessBlobHashesBodySpec P).
Proof.
  iIntros "#Hlookup Hnext".
  rewrite instr_pre'_eq. iIntros "Hbody".
  iPoseProof (write_success_blob_hashes_segment15_entry P with "Hbody")
    as "Hentry".
  iPoseProof (write_success_blob_hashes_segment17_prepare_15490 P with
    "Hentry") as "Hprepared".
  iDestruct "Hprepared" as
    (sp pointer base total processed remaining bytes tail byte) "Hstate".
  iAssert (instr_body 0x15494
    (writeSuccessBlobHashesLbuResult P "x22" 19 1 sp pointer base total
      processed remaining bytes tail byte))%I with "[Hnext]" as "Hreturn".
  { rewrite instr_pre'_eq. iIntros "Hresult".
    iPoseProof (write_success_blob_hashes_segment17_return_15490 P sp pointer
      base total processed remaining bytes tail byte with "Hresult") as
      "Hbody".
    iApply "Hnext". iExact "Hbody". }
  iPoseProof (write_success_blob_hashes_segment17_core_15490 P sp pointer base
    total processed remaining bytes tail byte with "Hlookup Hreturn")
    as "Hcore".
  iEval (rewrite instr_pre'_eq) in "Hcore".
  iApply "Hcore". iExact "Hstate".
Qed.
