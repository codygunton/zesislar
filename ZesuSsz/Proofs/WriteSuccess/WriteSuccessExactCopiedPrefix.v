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
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedPrefixCopy.
Lemma write_success_exact_copied_prefix `{!islaG Sigma} `{!threadG}
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
   instr_body 0x14d30
     (write_success_prologue_entry
       (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
       (writeSuccessReturnValue witness)
       (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
       (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
       (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
       (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
       (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
       (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
       (writeSuccessProloguePayload witness ∗ P)))%I.
Proof.
  iIntros "#Hnative #Htx".
  iPoseProof (write_success_exact_copied_prefix_copy args witness P Hwf with "Hnative Htx") as "Hcopy".
  iEval (unfold exactPrefixCopyEntry) in "Hcopy".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as "#(H00 & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & Hlists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (write_success_prologue
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness) (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness) (writeSuccessSavedS2 witness)
    (writeSuccessSavedS3 witness) (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness) (writeSuccessSavedS8 witness)
    (writeSuccessSavedS9 witness) (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessProloguePayload witness ∗ P)%I with "H00") as "Hprologue".
  iApply (instr_pre_wand 0x14d30 0x14d30 false false with "Hprologue"); [done | reflexivity |].
  iIntros "Hentry". iSplitL "Hentry"; [iExact "Hentry" |].
  iSplitL "Hcopy"; [|done].
  iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand 0x14d7c 0x14d7c false false with "Hcopy"); [done | reflexivity |].
  iIntros "Hpost".
  iEval (unfold write_success_prologue_exit) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hregs & H1 & H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H10 & H11 & H12 & Hsaved & Hpayload & _)".
  rewrite /write_success_prologue_exit.
  iFrame "Hsys Hregs H1 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H10 H11 H12".
  iSplitL "Hsaved"; [iExact "Hsaved" |].
  iSplitL "Hpayload"; [|done].
  iDestruct "Hpayload" as "[Hpayload HP]".
  iEval (unfold writeSuccessProloguePayload) in "Hpayload".
  iDestruct "Hpayload" as "(Hworkspace & Hobject & Hmmio & Htrace & Hdata & Hlength & Hlower & Hupper & _)".
  iFrame "Hworkspace Hobject Hmmio Htrace".
  iSplitL "Hdata HP"; [|iFrame "Hlength Hlower Hupper"].
  iSplitL "Hdata"; [iExact "Hdata" | iExact "HP"].
Qed.
Print Assumptions write_success_exact_copied_prefix.
