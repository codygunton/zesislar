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


Definition exactPrefixCopyState `{!islaG Sigma} `{!threadG} {Decoded}
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  exactNativeCopyPost
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness) (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness) (writeSuccessSavedS2 witness)
    (writeSuccessSavedS3 witness) (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness) (writeSuccessSavedS8 witness)
    (writeSuccessSavedS9 witness) (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessDecodedBytes witness) (writeSuccessNativeTailEvents witness)
    (writeSuccessNativeDataResources witness ∗ P)%I.

Definition exactPrefixCopyEntry `{!islaG Sigma} `{!threadG} {Decoded}
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  write_success_prologue_exit
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness) (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness) (writeSuccessSavedS2 witness)
    (writeSuccessSavedS3 witness) (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness) (writeSuccessSavedS8 witness)
    (writeSuccessSavedS9 witness) (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (((bv_unsigned (writeSuccessEntrySp witness) - 2000) ↦ₘ? 1896 ∗
     bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeSuccessNativeTailEvents witness) ∗
     (writeSuccessNativeDataResources witness ∗ P) ∗
     ⌜length (writeSuccessDecodedBytes witness) = 848%nat⌝ ∗
     ⌜mapRamBase defaultMap <= bv_unsigned (writeSuccessDecodedPointer witness)⌝ ∗
     ⌜bv_unsigned (writeSuccessDecodedPointer witness) + 848 < machineRamEnd defaultMap⌝ ∗ True)%I).

Lemma write_success_exact_prefix_loads `{!islaG Sigma} `{!threadG}
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
       (writeSuccessExactTailCaller args witness ∗ P)) -∗
   instr_body 0x14d80 (exactPrefixCopyState witness P))%I.
Proof.
  have [Hframe [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  iIntros "#Hnative #Htx".
  iPoseProof (exact_prefix_calls with "Hnative") as "(#HcopyGuard & #HwriteGuard & #HintGuard & #HbytesGuard)".
  iPoseProof "Hnative" as "#Hbundle".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as "#(H00 & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & Hlists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (write_success_exact_header_value
    (writeSuccessExactHeaderLiveFrameRest (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactCallerRemainder args witness ∗ P))
    (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessExactTransactionsEvents (writeSuccessFrameSp witness)
      (writeSuccessTransactions witness) (writeSuccessExactTailEvents witness))
    with "Hlookup Hmain HcopyGuard HwriteGuard HintGuard HbytesGuard") as "Hheader".
  iAssert (instr_body 0x14e00 (exactPrefixCopyState witness P)) with "[Hheader]" as "HheaderCopy".
  { iApply (instr_pre_wand 0x14e00 0x14e00 false false with "Hheader"); [done | reflexivity |].
    iIntros "Hstate".
    iEval (unfold exactPrefixCopyState) in "Hstate".
    iApply (exact_copy_header_frame args witness P Hwf Hframe Halign Hupper with "Htx Hstate"). }
  iAssert (instr_body 0x14d80 (exactPrefixCopyState witness P)) with "[HheaderCopy]" as "Hloads".
  { iApply (exact_native_load_complete_correct with "Hnative HheaderCopy"). }
  iExact "Hloads".
Qed.
Print Assumptions write_success_exact_prefix_loads.

Lemma write_success_exact_prefix_copy `{!islaG Sigma} `{!threadG}
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
       (writeSuccessExactTailCaller args witness ∗ P)) -∗
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
  iPoseProof (write_success_exact_prefix_loads args witness P Hwf with "Hnative Htx") as "Hloads".
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
Print Assumptions write_success_exact_prefix_copy.

Lemma write_success_exact_prefix `{!islaG Sigma} `{!threadG}
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
       (writeSuccessExactTailCaller args witness ∗ P)) -∗
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
  iPoseProof (write_success_exact_prefix_copy args witness P Hwf with "Hnative Htx") as "Hcopy".
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
Print Assumptions write_success_exact_prefix.
