Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsBoundary151dc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsChunk151dc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsChunk15200.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsChunk15210.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsStorage.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsTail.

Definition writeSuccessAccessListsAt151dcBody
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  instr_body 0x151dc (writeSuccessAccessListsAt151dcSpec x19 P).

Lemma write_success_access_lists_loop_continuation_body
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x151d4 (writeSuccessAccessListsLoopSpec x19 P) -∗
  □ writeSuccessAccessListsAt151dcBody x19 P.
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hint #Hloop".
  iModIntro.
  rewrite /writeSuccessAccessListsAt151dcBody.
  iApply (write_success_access_lists_chunk_151dc x19 P with
    "Hlookup Hcode Hmemcpy").
  iApply (write_success_access_lists_chunk_15200 x19 P with
    "Hlookup Hcode Houtput").
  iApply (write_success_access_lists_chunk_15210 x19 P with
    "Hlookup Hcode Hint").
  iApply (write_success_access_lists_storage x19 P with
    "Hlookup Hcode Houtput").
  iApply (write_success_access_lists_tail x19 P with
    "Hlookup Hcode Hloop").
Qed.

Lemma write_success_access_lists_loop_continuation_pre
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  □ writeSuccessAccessListsAt151dcBody x19 P -∗
  □ instr_pre 0x151dc (writeSuccessAccessListsAt151dcSpec x19 P).
Proof.
  iStartProof. iIntros "#Hbody". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite -/writeSuccessAccessListsAt151dcBody.
  iExact "Hbody".
Qed.
