Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeCode WriteSuccessNativeContract
  WriteSuccessRepresentation WriteSuccessValueBlock
  WriteSuccessExactPrefixStackFacts
  WriteSuccessExactTailRawLoad WriteSuccessExactTailRawLoadSpec
  WriteSuccessExactTailRawReadySpec WriteSuccessExactTailRawLoadExitAdapter
  WriteSuccessExactTailRawCallSpec
  WriteSuccessExactTailRawCallReturnSpec
  WriteSuccessExactTailRawCallEntryAdapter
  WriteSuccessExactTailRawCallComposition
  WriteSuccessExactTailWithdrawalLoadSpec
  WriteSuccessExactTailWithdrawalLoadComposition
  WriteSuccessExactTailWithdrawalCountEntry
  WriteSuccessExactTailWithdrawalCountModel
  WriteSuccessExactTailWithdrawalCountSpec
  WriteSuccessExactTailWithdrawalsBranchSpec
  WriteSuccessExactEncoderIntFramedCall.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_88.a15688_spec.
Open Scope Z_scope.

Lemma exact_tail_withdrawal_branch_zero_adapter
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  exactTailWithdrawalBranchResources args witness P -∗
  ⌜writeSuccessValueWord (writeSuccessValues witness) 12 = BV 64 0⌝ -∗
  exactTailWithdrawalsBranchZeroEntry args witness P.
Proof.
  iIntros "Hresources %HmachineZero".
  rewrite /exactTailWithdrawalsBranchZeroEntry.
  iFrame "Hresources". iPureIntro.
  apply (exact_tail_withdrawal_count_zero_iff args witness Hwf).
  exact HmachineZero.
Qed.

Lemma exact_tail_withdrawal_branch_nonzero_adapter
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  exactTailWithdrawalBranchResources args witness P -∗
  ⌜writeSuccessValueWord (writeSuccessValues witness) 12 <> BV 64 0⌝ -∗
  exactTailWithdrawalsBranchNonzeroEntry args witness P.
Proof.
  iIntros "Hresources %HmachineNonzero".
  rewrite /exactTailWithdrawalsBranchNonzeroEntry.
  iFrame "Hresources". iPureIntro.
  have HcountNonzero : writeSuccessWithdrawalsCount witness <> 0%nat.
  { intro HcountZero. apply HmachineNonzero.
    apply (exact_tail_withdrawal_count_zero_iff args witness Hwf).
    exact HcountZero. }
  lia.
Qed.

Lemma write_success_exact_post_transactions_segment
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15694
    (exactTailWithdrawalsBranchNonzeroEntry args witness P) -∗
  □ instr_pre 0x156e8
    (exactTailWithdrawalsBranchZeroEntry args witness P) -∗
  instr_body 0x15668
    (writeSuccessExactPostTransactionsBoundary
      (writeSuccessFrameSp witness) (writeSuccessValues witness)
      (length (writeSuccessTransactions witness))
      (writeSuccessExactTailEvents witness)
      (exactTailRawLoadMachineFrame args witness P)).
Proof.
  have Hvalues : length (writeSuccessValues witness) = 74%nat.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have [Hframe [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  have Hlower : mapRamBase defaultMap <= bv_unsigned (writeSuccessFrameSp witness).
  { change (0 <= bv_unsigned (writeSuccessFrameSp witness)).
    pose proof (bv_unsigned_in_range _ (writeSuccessFrameSp witness)). lia. }
  have Hframe16 :
      (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 16))%bv =
      (writeSuccessFrameSp witness - BV 64 16)%bv by bv_solve.
  have Hzero := exact_tail_withdrawal_count_zero_iff args witness Hwf.
  iStartProof. iIntros "#Hnative #Hnonzero #Hzero".
  iAssert (instr_body 0x15690
    (exactTailWithdrawalBranchResources args witness P))%I with "[]" as "#Hstatus".
  { iEval (rewrite /writeSuccessCompleteNativeCode) in "Hnative".
    iDestruct "Hnative" as
      "(#Hprologue & #Hlookup & #Hmain & #Houtput & #Hmemcpy & #Hboolean &
        #Hoptional & #Hlists & #Hbytes & #Hint & #Hu256 & #Hu128)".
    zesu_block. Unshelve.
    all: try zesu_run.
    all: iRename select ("x1" ↦ᵣ RVal_Bits (BV 64 0x1568c) ∗ _)%I into "Hpost";
      iDestruct "Hpost" as
        "(? & ? & ? & ? & ? & ? & ? & ? & HbranchFrame & _)";
      zesu_open_requested_saved_x9_package; try zesu_run.
    all: iRename select ("x10" ↦ᵣ RVal_Bits _)%I into "H10branch";
      iEval (rewrite Hframe16) in "H10branch".
    all: iAssert (exactTailWithdrawalBranchResources args witness P)%I
      with "[-]" as "Hresources";
      [rewrite /exactTailWithdrawalBranchResources
        /encoderIntExactFramedPost /exactTailWithdrawalBranchFrame
        /exactTailWithdrawalCommonFrame;
       iFrame; iPureIntro; exact Hwf |].
    all: lazymatch goal with
    | |- environments.envs_entails _
        (exactTailWithdrawalsBranchZeroEntry _ _ _) =>
        iApply (exact_tail_withdrawal_branch_zero_adapter args witness P Hwf
          with "Hresources"); iPureIntro; assumption
    | |- environments.envs_entails _
        (exactTailWithdrawalsBranchNonzeroEntry _ _ _) =>
        iApply (exact_tail_withdrawal_branch_nonzero_adapter args witness P Hwf
          with "Hresources"); iPureIntro; assumption
    end.
    }
  iAssert (instr_body 0x1568c
    (exactTailWithdrawalCountReturn args witness P))%I with "[]" as "#Hreturn".
  { iEval (rewrite /writeSuccessCompleteNativeCode) in "Hnative".
    iDestruct "Hnative" as
      "(#Hprologue & #Hlookup & #Hmain & #Houtput & #Hmemcpy & #Hboolean &
        #Hoptional & #Hlists & #Hbytes & #Hint & #Hu256 & #Hu128)".
    iAssert (□ instr_pre 0x15690
      (exactTailWithdrawalBranchResources args witness P))%I with "[]" as "#Hnext".
    { iModIntro. iApply instr_pre_to_body. iNext. iExact "Hstatus". }
    zesu_block. Unshelve.
    all: zesu_open_resource_groups; try zesu_run.
    all: iIntros "Hoptional"; try zesu_run.
    all: iEval (unfold exactTailWithdrawalBranchResources);
      iRename select (reg_col ((KindReg "x19", BitsShape 64) :: _))%I
        into "HsavedTail"; try zesu_run.
    all: iFrame "Hoptional"; try zesu_run. }
  iAssert (instr_body 0x15688
    (exactTailWithdrawalCountCallEntry args witness P))%I with "[]" as "#Hcount".
  { iEval (rewrite /writeSuccessCompleteNativeCode) in "Hnative".
    iDestruct "Hnative" as
      "(#Hprologue & #Hlookup & #Hmain & #Houtput & #Hmemcpy & #Hboolean &
        #Hoptional & #Hlists & #Hbytes & #Hint & #Hu256 & #Hu128)".
    iPoseProof "Hlookup" as "#Hlookup15688".
    iEval (rewrite /instr_lookup_resources) in "Hlookup15688".
    iPoseProof ("Hlookup15688" $! 0x15688 with "[]") as "#Hinstr15688".
    { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15688. done. }
    iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15688)
      in "Hinstr15688".
    rewrite instr_pre'_eq. iIntros "Hentry".
    iEval (rewrite /exactTailWithdrawalCountCallEntry) in "Hentry".
    iDestruct "Hentry" as (old5 old11)
      "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace &
        %Halign' & %Hlower' & %Hupper' & %Hcount' & HcountFrame & Hnext & _)".
    iPoseProof (encoder_int_exact_framed_correct
      (writeSuccessValueWord (writeSuccessValues witness) 12)
      (writeSuccessFrameSp witness) (BV 64 0x1568c) old5 old11
      (exactTailAfterWithdrawalCountEvents witness)
      (exactTailWithdrawalCountFrame args witness P)
      with "Hint Houtput") as "Hcallee".
    iEval (rewrite exact_tail_after_raw_count) in "Htrace".
    replace (bv_wrap 64 87688) with 87688 by bv_solve.
    zesu_run.
    Unshelve. all: unLET.
    all: try (rewrite Hcount').
    all: try reflexivity.
    all: try bv_solve.
    all: try done.
    all: iFrame. }
  iAssert (instr_body 0x15688
    (exactTailWithdrawalLoadPost args witness P))%I with "[]" as "#Hload".
  { iApply (instr_pre_wand 0x15688 0x15688 false false with "Hcount");
      [done | reflexivity |].
    iIntros "Hload".
    iAssert (□ instr_pre 0x1568c
      (exactTailWithdrawalCountReturn args witness P))%I with "[]" as "#HreturnPre".
    { iModIntro. iApply instr_pre_to_body. iNext. iExact "Hreturn". }
    iApply (exact_tail_withdrawal_count_entry with "Hload HreturnPre"). }
  iAssert (□ instr_pre 0x15678
    (exactTailRawCallReturn args witness P))%I with "[]" as "#H15678".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (exact_tail_raw_return_through_withdrawal_load with "Hnative Hload"). }
  iAssert (□ instr_pre 0x15674
    (exactTailRawLoadExit (writeSuccessFrameSp witness)
      (writeSuccessValues witness) (writeSuccessExactTailEvents witness)
      (exactTailRawLoadMachineFrame args witness P)))%I with "[]" as "#H15674".
  { iModIntro.
    iApply instr_pre_to_body. iNext.
    iPoseProof (exact_tail_raw_call args witness P with "Hnative H15678") as "Hbody".
    iApply (instr_pre_wand 0x15674 0x15674 false false with "Hbody");
      [done | reflexivity |].
    iIntros "Hexit".
    iPoseProof (exact_tail_raw_load_exit_adapter args witness P with "Hexit") as "Hready".
    iPoseProof (exact_tail_raw_ready_to_call args witness P Hwf with "Hready") as "Hentry".
    iExact "Hentry". }
  iApply (exact_tail_raw_load (writeSuccessFrameSp witness)
    (writeSuccessValues witness) (length (writeSuccessTransactions witness))
    (writeSuccessExactTailEvents witness) (exactTailRawLoadMachineFrame args witness P)
    Hvalues Halign Hlower Hupper with "Hnative H15674").
Qed.
Print Assumptions write_success_exact_post_transactions_segment.
