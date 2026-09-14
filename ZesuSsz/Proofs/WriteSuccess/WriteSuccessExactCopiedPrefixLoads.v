Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessNativeCode WriteSuccessRepresentation
  WriteSuccessExactNativeLoad WriteSuccessExactNativeLoadSpec WriteSuccessExactNativeCopy
  WriteSuccessExactCopyHeaderFrame WriteSuccessExactPrefixStackFacts WriteSuccessExactHeaderValue
  WriteSuccessPrologue WriteSuccessCalls WriteSuccessExactNativeHeaderEntry
  WriteSuccessExactPrefixCalls WriteSuccessExactHeaderLiveEntry WriteSuccessExactTransactionsSpec
  WriteSuccessValueBlock WriteSuccessPrologueSpec.
Require Import ZesuSsz.Automation.CodeLookup.
From IslaTraces.write_success_09 Require Import instrs.


From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessExactPrefix WriteSuccessExactCopiedCopySpec
 WriteSuccessExactCopiedNativeLoadComplete WriteSuccessExactCopiedCopyHeaderFrame
 WriteSuccessExactCopiedHeaderLiveEntry.
Definition exactCopiedPrefixLoadPost `{!islaG Sigma} `{!threadG} {Decoded}
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  exactNativeCopiedCopyPost 16
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness) (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness) (writeSuccessSavedS2 witness)
    (writeSuccessSavedS3 witness) (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness) (writeSuccessSavedS8 witness)
    (writeSuccessSavedS9 witness) (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessDecodedBytes witness) (writeSuccessNativeTailEvents witness)
    (writeSuccessNativeDataResources witness ∗ P)%I.
Lemma write_success_exact_copied_prefix_loads `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma)
  (Hwf : writeSuccessWitnessWellFormed args witness) :
  ⊢ (writeSuccessCompleteNativeCode -∗
   □ instr_pre 0x14f04
     (writeSuccessExactTransactionsEntryBoundary
       (writeSuccessFrameSp witness) (writeSuccessTransactionBase witness)
       (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
       (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
       (writeSuccessExactTailEvents witness)
       (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P)) -∗
   instr_body 0x14d80 (exactPrefixCopyState witness P))%I.
Proof.
  have [Hframe [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  iIntros "#Hnative #Htx".
  iPoseProof (exact_prefix_calls with "Hnative") as "(#HcopyGuard & #HwriteGuard & #HintGuard & #HbytesGuard)".
  iPoseProof "Hnative" as "#Hbundle".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as "#(H00 & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & Hlists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (write_success_exact_header_value
    (writeSuccessExactCopiedHeaderLiveFrameRest (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) (writeSuccessDecodedBytes witness)
      (writeSuccessExactCallerRemainder args witness ∗ P))
    (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessExactTransactionsEvents (writeSuccessFrameSp witness)
      (writeSuccessTransactions witness) (writeSuccessExactTailEvents witness))
    with "Hlookup Hmain HcopyGuard HwriteGuard HintGuard HbytesGuard") as "Hheader".
  iAssert (instr_body 0x14e00 (exactCopiedPrefixLoadPost witness P)) with "[Hheader]" as "HheaderCopy".
  { iApply (instr_pre_wand 0x14e00 0x14e00 false false with "Hheader"); [done | reflexivity |].
    iIntros "Hstate".
    iEval (unfold exactCopiedPrefixLoadPost) in "Hstate".
    iApply (exact_copied_copy_header_frame args witness P Hwf Hframe Halign Hupper with "Htx Hstate"). }
  iAssert (instr_body 0x14d80 (exactPrefixCopyState witness P)) with "[HheaderCopy]" as "Hloads".
  { iEval (unfold exactCopiedPrefixLoadPost, exactNativeCopiedCopyPost) in "HheaderCopy".
    iApply (exact_copied_native_load_complete_correct with "Hnative HheaderCopy"). }
  iExact "Hloads".
Qed.
Print Assumptions write_success_exact_copied_prefix_loads.
