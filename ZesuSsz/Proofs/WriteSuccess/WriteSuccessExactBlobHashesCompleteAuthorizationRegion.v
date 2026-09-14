Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactBlobHashesAuthorizationRegion
  WriteSuccessExactBlobHashesAuthorizationEntry WriteSuccessBlobHashesSpec
  WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma blob_complete_authorization_region_correct `{!islaG Sigma} `{!threadG}
    sp base total bytes low high count tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload low high)
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail))
    (blobAuthorizationCaller sp low high count base total bytes tail P)).
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (blob_authorization_region_correct with "[] [] Hu128 Hint Houtput").
  all: iApply instr_lookup_collect; last iExact "Hlookup".
  all: repeat constructor; reflexivity.
Qed.
Print Assumptions blob_complete_authorization_region_correct.
