Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment15Entry.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2APrepare94.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2ARaw94.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2AReturn94.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2APrepare98.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2ARaw98.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesChunk2AReturn98.

Lemma write_success_blob_hashes_chunk2a `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1549c (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hbody".
  iPoseProof (write_success_blob_hashes_segment15_entry P with "Hbody") as
    "Hentry".
  iPoseProof (write_success_blob_hashes_chunk2a_prepare_15494 P with "Hentry")
    as "Hprepared94".
  iDestruct "Hprepared94" as
    (sp pointer base total processed remaining bytes tail byte94) "Hstate94".
  iAssert (instr_body 0x15498
    (writeSuccessBlobHashesLbuResult P "x23" 20 2 sp pointer base total
      processed remaining bytes tail byte94))%I with "[Hnext]" as "Hnext94".
  { rewrite instr_pre'_eq. iIntros "Hresult94".
    iPoseProof (write_success_blob_hashes_chunk2a_return_15494 P sp pointer
      base total processed remaining bytes tail byte94 with "Hresult94") as
      "Hbody94".
    iPoseProof (write_success_blob_hashes_segment15_entry P with "Hbody94")
      as "Hentry98".
    iPoseProof (write_success_blob_hashes_chunk2a_prepare_15498 P with
      "Hentry98") as "Hprepared98".
    iDestruct "Hprepared98" as
      (sp98 pointer98 base98 total98 processed98 remaining98 bytes98 tail98 byte98)
      "Hstate98".
    iAssert (instr_body 0x1549c
      (writeSuccessBlobHashesLbuResult P "x26" 23 3 sp98 pointer98 base98
        total98 processed98 remaining98 bytes98 tail98 byte98))%I
      with "[Hnext]" as "Hnext98".
    { rewrite instr_pre'_eq. iIntros "Hresult98".
      iPoseProof (write_success_blob_hashes_chunk2a_return_15498 P sp98
        pointer98 base98 total98 processed98 remaining98 bytes98 tail98
        byte98 with "Hresult98") as "Hbody98".
      iApply "Hnext". iExact "Hbody98". }
    iPoseProof (write_success_blob_hashes_chunk2a_raw_15498 P sp98 pointer98
      base98 total98 processed98 remaining98 bytes98 tail98 byte98 with
      "Hlookup Hnext98") as "Hraw98".
    iEval (rewrite instr_pre'_eq) in "Hraw98".
    iApply "Hraw98".
    iExact "Hstate98". }
  iPoseProof (write_success_blob_hashes_chunk2a_raw_15494 P sp pointer base total
    processed remaining bytes tail byte94 with "Hlookup Hnext94")
    as "Hraw94".
  iEval (rewrite instr_pre'_eq) in "Hraw94".
  iApply "Hraw94".
  iExact "Hstate94".
Qed.
