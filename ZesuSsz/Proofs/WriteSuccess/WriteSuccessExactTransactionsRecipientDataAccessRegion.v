Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientValueRegion
  WriteSuccessExactTransactionsRecipientBranch WriteSuccessExactTransactionsRecipientBranchHandoff
  WriteSuccessExactTransactionsRecipientDataFrame WriteSuccessExactTransactionsValueDataAccessContinuation
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsValueCall
  WriteSuccessExactTransactionsDataToAccessCount WriteSuccessExactTransactionsAccessCountCall
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionDataAccessOutputTrace (data size sp count : bv 64)
    (bytes : list (bv 8)) tail : spec :=
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
    (writeOutputEvents data size bytes
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)).

Lemma transactions_recipient_data_access_region_correct `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 data size count oldra old5 old11 old12 old13 olddata old6 old9 : bv 64)
    (last : bv 32) bytes tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151d0 (transactionAccessCountPost sp count tail
    (transactionDataAccessFrame data size sp old9 bytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last P)))) -∗
  instr_body 0x15154 (transactionRecipientBranchState sp tag olddata
    (transactionRecipientBranchCallerFrame sp tag first second w0 w1 w2 w3
      oldra old5 old11 old12 old13 last
      (transactionDataAccessOutputTrace data size sp count bytes tail)
      (transactionValueDataAccessCaller data size sp count old6 old9 bytes P))).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (transactions_value_data_access_continuation data size sp w0 w1 w2 w3 old6 old9 count bytes tail
    (transactionRecipientValueExitFrame sp tag first second last P) with "Hcode Hnext") as "#HdataNext".
  iAssert (□ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3
    (transactionDataAccessOutputTrace data size sp count bytes tail)
    (transactionRecipientValueExitFrame sp tag first second last
      (transactionValueDataAccessCaller data size sp count old6 old9 bytes P))))%I as "#HrecipientNext".
  { iModIntro. iApply (instr_pre_wand 0x151b4 0x151b4 true true with "HdataNext"); [done | done |].
    iApply transactions_value_recipient_data_frame_pack. }
  iApply (transactions_recipient_value_region_correct with "Hcode HrecipientNext").
Qed.
Print Assumptions transactions_recipient_data_access_region_correct.
