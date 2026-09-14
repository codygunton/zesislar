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
 WriteSuccessExactCopiedNativeLoad WriteSuccessExactCopiedCopyHeaderFrame
 WriteSuccessExactCopiedHeaderLiveEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedPrefixLoads.
Lemma write_success_exact_copied_prefix_copy `{!islaG Sigma} `{!threadG}
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
   instr_body 0x14d7c (exactPrefixCopyEntry witness P))%I.
Proof.
  have Hdecoded : bv_unsigned (writeSuccessDecodedPointer witness) =
    bv_unsigned (writeSuccessEntrySp witness) + 32.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have HentryAlign : bv_unsigned (writeSuccessEntrySp witness) `mod` 16 = 0.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have HentryLower : mapRamBase defaultMap + 0x880 <= bv_unsigned (writeSuccessEntrySp witness).
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have HentryUpper : bv_unsigned (writeSuccessEntrySp witness) + 0x7d0 < machineRamEnd defaultMap.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  iIntros "#Hnative #Htx".
  iPoseProof "Hnative" as "#Hbundle".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as "#(H00 & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & Hlists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (exact_prefix_calls with "Hnative") as "(#HcopyGuard & #HwriteGuard & #HintGuard & #HbytesGuard)".
  iPoseProof (write_success_exact_copied_prefix_loads args witness P Hwf with "Hnative Htx") as "Hloads".
  iPoseProof (instr_lookup_collect _ IslaTraces.write_success_09.instrs.instr_map with "Hlookup") as "H09";
    first (repeat constructor; reflexivity).
  iPoseProof (exact_native_copy_correct
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness) (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness) (writeSuccessSavedS2 witness)
    (writeSuccessSavedS3 witness) (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness) (writeSuccessSavedS8 witness)
    (writeSuccessSavedS9 witness) (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessDecodedBytes witness) (writeSuccessNativeTailEvents witness)
    (writeSuccessNativeDataResources witness ∗ P)%I Hdecoded HentryAlign HentryLower HentryUpper
    with "H09 HcopyGuard Hloads") as "Hcopy".
  iExact "Hcopy".
Qed.
Print Assumptions write_success_exact_copied_prefix_copy.
