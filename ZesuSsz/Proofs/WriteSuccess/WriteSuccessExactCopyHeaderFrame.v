Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMemory.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces WriteSuccessNativeContract
 WriteSuccessRepresentation WriteSuccessValueBlock WriteSuccessPrologueSpec
 WriteSuccessExactNativeCopy WriteSuccessExactNativeLoadFrame WriteSuccessExactNativeHeaderEntry
 WriteSuccessExactHeaderValue WriteSuccessExactHeaderLiveEntry WriteSuccessExactHeaderGuard
 WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsSpec WriteSuccessTransactionsSpec
 WriteSuccessExactHeaderSourceFacts WriteSuccessExactPrefixModel WriteSuccessExactValueSpec
 WriteSuccessExactValueModel WriteSuccessToLoadWithFrame.
Lemma exact_copy_header_frame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) (Hwf : writeSuccessWitnessWellFormed args witness)
    (Hframe : bv_unsigned (writeSuccessEntrySp witness) =
      (bv_unsigned (writeSuccessFrameSp witness) + 2000)%Z)
    (Halign : bv_unsigned (writeSuccessFrameSp witness) `mod` 16 = 0)
    (Hupper : bv_unsigned (writeSuccessFrameSp witness) + 1896 < machineRamEnd defaultMap) :
  □ instr_pre 0x14f04
    (writeSuccessExactTransactionsEntryBoundary (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness) []
      (writeSuccessTransactions witness) (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness) (writeSuccessExactTailCaller args witness ∗ P)) -∗
  exactNativeCopyPost (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
    (writeSuccessReturnValue witness) (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
    (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness) (writeSuccessSavedS4 witness)
    (writeSuccessSavedS5 witness) (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
    (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness) (writeSuccessSavedS10 witness)
    (writeSuccessSavedS11 witness) (writeSuccessDecodedBytes witness)
    (writeSuccessNativeTailEvents witness) (writeSuccessNativeDataResources witness ∗ P) -∗
  writeSuccessExactHeaderValueSpec
    (writeSuccessExactHeaderLiveFrameRest (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactCallerRemainder args witness ∗ P))
    (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessExactTransactionsEvents (writeSuccessFrameSp witness)
      (writeSuccessTransactions witness) (writeSuccessExactTailEvents witness)).
Proof.
  have HsourceLength : length (writeSuccessSourceBytes witness) = 720%nat.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have Hsource : writeSuccessSourceBytes witness = take 720 (writeSuccessDecodedBytes witness).
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  iIntros "#Hentry Hcopy".
  iPoseProof (exact_header_transaction_guard args witness P with "Hentry") as "#Hloop".
  iEval (unfold exactNativeCopyPost) in "Hcopy".
  iApply (native_load_header_entry _ _ _ _ _ _ _ _ HsourceLength Halign Hupper).
  iApply (exact_native_load_frame_mono with "[] Hcopy").
  iIntros "(Hsource & Hhigh & Hsaved & Hmmio & Htrace & Hdata & HP)".
  iEval (unfold writeSuccessNativeDataResources) in "Hdata".
  iDestruct "Hdata" as "(Hheap & Hraw & Hwithdrawals & %HrawFacts & %HwithdrawalBase & %HwithdrawalCount & %HwithdrawalLength & %HwithdrawalLower & %HwithdrawalUpper & Hpost & Hstatic)".
  iEval (unfold writeSuccessLoadHeaderHeapResources) in "Hheap".
  iDestruct "Hheap" as "(Hlow & Hcall & Hpayload & Harray & Hown & #Hinvariant & %HsourceLen & %HvaluesBytes & %HvaluesLen & %HpayloadLen & %HbaseEq & %HcountEq & %Halign16 & %Halign8 & %Hlower & %Hmax & _)".
  iPoseProof (write_success_exact_header_source_facts with "Hinvariant") as "%Hfacts".
  iEval (rewrite (write_success_exact_entry_trace args witness Hwf Hfacts)) in "Htrace".
  iEval (rewrite -Hsource) in "Hsource".
  iAssert (writeSuccessTerminalSavedSlots witness) with "[Hsaved]" as "HsavedNative".
  { iEval (rewrite /writeSuccessSavedSlots Hframe -!Z.add_sub_assoc /=) in "Hsaved".
    rewrite /writeSuccessTerminalSavedSlots. repeat iDestruct "Hsaved" as "[? Hsaved]". iFrame. }
  iFrame "Hsource Hhigh Hmmio Htrace Hstatic".
  iIntros "(Hprefix & Hsuffix & Hobject)".
  iAssert (bv_unsigned (writeSuccessExactValueWord (writeSuccessValues witness) 4) ↦ₘ∗ writeSuccessPayload witness)%I with "[Hpayload]" as "HpayloadExact".
  { rewrite exact_value_word_take69; [iExact "Hpayload" | lia]. }
  iApply (write_success_exact_header_live_transition with "Hloop Hlow HpayloadExact").
  - rewrite lookup_take; [exact HbaseEq | lia].
  - rewrite lookup_take; [exact HcountEq | lia].
  - exact HvaluesLen.
  - exact HvaluesBytes.
  - rewrite exact_value_word_take69; [exact HpayloadLen | lia].
  - exact Halign16.
  - exact Halign8.
  - exact Hlower.
  - exact Hmax.
  - rewrite /writeSuccessExactHeaderLiveFrameRest /writeSuccessExactCallerRemainder.
    iFrame. iFrame "Hinvariant".
    iSplit; [iPureIntro; exact Hfacts |].
    iSplit; [iPureIntro; exact Hwf | done].
Qed.
Print Assumptions exact_copy_header_frame.
