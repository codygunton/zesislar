Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessExactTailWithdrawalsBranchSpec
  WriteSuccessExactEncoderIntFramedCall WriteSuccessExactTailWithdrawalCountModel
  WriteSuccessExactTailWithdrawalCountSpec WriteSuccessExactTailWithdrawalLoadSpec
  WriteSuccessExactTailStackCallBounds
  WriteSuccessExactValueSpec
  WriteSuccessExactWithdrawalsLoopSpec
  WriteSuccessExactWithdrawalsNativeRows WriteSuccessNativeContract
  WriteSuccessRepresentation WriteSuccessValueSpec.

Lemma write_success_exact_withdrawals_zero_resources
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  exactTailWithdrawalsBranchZeroEntry args witness P -∗
  writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P).
Proof.
  have [Hcount [Hall Hconcat]] := write_success_exact_withdrawal_rows_facts args witness Hwf.
  have [HstackLow HstackHigh] := exact_tail_stack_call_bounds args witness Hwf.
  iStartProof. iIntros "Hentry".
  iEval (rewrite /exactTailWithdrawalsBranchZeroEntry
    /exactTailWithdrawalBranchResources /encoderIntExactFramedPost /exactTailWithdrawalBranchFrame
    /exactTailWithdrawalCommonFrame /exactTailWithdrawalValueRemainder /writeSuccessExactCopiedTailWords
    /WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources
    /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
    /WriteSuccessPostTransactionResources.writeSuccessHashesResources
    /WriteSuccessPostTransactionResources.writeSuccessOptionalDescriptorResources) in "Hentry".
  iEval (rewrite /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
    /WriteSuccessPostTransactionResources.writeSuccessHashesResources
    /WriteSuccessPostTransactionResources.writeSuccessOptionalDescriptorResources) in "Hentry".
  iDestruct "Hentry" as "[Hentry %Hzero]".
  iDestruct "Hentry" as "[Hentry Hx18]".
  iDestruct "Hentry" as
    "[Hsys [Hx1 [Hx2 [Hx5 [Hx10 [Hx11 [HcallStack [Hmmio [Htrace [Hentry _]]]]]]]]]]".
  iDestruct "Hentry" as "[HcallerRegs1 [HcallerRegs2 [HcallerRegs3 Hentry]]]".
  iDestruct "Hentry" as "[Hx8 [Hx9 Hentry]]".
  have HbaseWord : writeSuccessValueWord (writeSuccessValues witness) 11 =
      writeSuccessWithdrawalsBase witness by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  have HcountWord : writeSuccessValueWord (writeSuccessValues witness) 12 =
      BV 64 0 := (proj2 (exact_tail_withdrawal_count_zero_iff args witness Hwf)) Hzero.
  have HrowsNil : writeSuccessExactWithdrawalRows witness = [] by
    apply length_zero_iff_nil; rewrite Hcount Hzero.
  have HbytesNil : writeSuccessWithdrawalsBytes witness = [] by
    rewrite -Hconcat HrowsNil.
  have Hevents := exact_tail_after_withdrawal_count_rows args witness Hwf.
  rewrite HrowsNil /= in Hevents.
  iEval (rewrite Hevents) in "Htrace".
  iEval (rewrite HbaseWord) in "Hx8".
  iEval (rewrite HcountWord) in "Hx9".
  iEval (rewrite HbytesNil) in "Hentry".
  iEval (rewrite /writeSuccessExactPostWithdrawalsBoundary).
  rewrite HbytesNil /=.
  repeat iDestruct "Hentry" as "[? Hentry]".
  repeat iDestruct select (∃ _, _)%I as (?) "?".
  repeat iDestruct select (⌜_⌝)%I as %?.
  iRename select (P)%I into "HP".
  iRename select ((bv_unsigned (writeSuccessFrameSp witness) + 1640) ↦ₘ? 256)%I
    into "Hstack1640".
  iEval (simpl [exactTailWithdrawalCountOtherCallerShapes]) in "HcallerRegs1".
  iDestruct "HcallerRegs1" as "[Hx12 [Hx13 [Hx14 [Hx15 HcallerRegs1]]]]".
  iRename select ((bv_unsigned (writeSuccessFrameSp witness) - 80) ↦ₘ? 64)%I
    into "Hstack64".
  iDestruct (mem_mapsto_uninit_split 32 with "Hstack64")
    as "[HstackLow32 HstackHigh32]"; first lia.
  iAssert (writeSuccessExactTailCallerBundle args witness)%I
    with "[-Hsys Hx1 Hx2 Hx5 Hx10 Hx11 HcallStack Hmmio Htrace Hx18
      Hx8 Hx9 HP Hstack1640 Hx12 Hx13 Hx14 Hx15
      HcallerRegs1 HcallerRegs2 HcallerRegs3 HstackHigh32]"
    as "HtailCaller".
  { iApply (bi.equiv_entails_1_2 _ _ (writeSuccessExactTailCallerBundle_unfold args witness)).
    rewrite /writeSuccessExactTailCallerWithCopiedWords
      /writeSuccessExactCopiedTailWords /writeSuccessExactValueMemory
      /WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources
      /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
      /WriteSuccessPostTransactionResources.writeSuccessHashesResources
      /WriteSuccessPostTransactionResources.writeSuccessOptionalDescriptorResources.
    repeat first [zesu_open_matching_copied_word_package |
      zesu_open_matching_resource_package].
    rewrite HbytesNil.
    iFrame.
    iFrame "%". }
  iAssert (writeSuccessExactPostWithdrawalsCallerFrameRaw args witness)%I
    with "[HtailCaller HcallerRegs1 HcallerRegs2 HcallerRegs3 HstackHigh32]"
    as "HcallerRaw".
  { iEval (rewrite writeSuccessExactTailCallerBundle_unfold
      /writeSuccessExactTailCallerWithCopiedWords) in "HtailCaller".
    repeat iDestruct "HtailCaller" as "[? HtailCaller]".
    iEval (rewrite /reg_col) in "HcallerRegs1 HcallerRegs2 HcallerRegs3".
    rewrite /writeSuccessExactPostWithdrawalsCallerFrameRaw
      /writeSuccessExactPostWithdrawalsMemoryFrame /writeSuccessExactValueMemory
      /writeSuccessExactCopiedTailWords
      /WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources
      /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
      /WriteSuccessPostTransactionResources.writeSuccessHashesResources
      /WriteSuccessPostTransactionResources.writeSuccessOptionalDescriptorResources
      /reg_col.
    repeat first [zesu_open_matching_copied_word_package |
      zesu_open_matching_resource_package].
    iEval (simpl) in "HcallerRegs1 HcallerRegs2 HcallerRegs3". simpl.
    have HstackHalf : bv_unsigned (writeSuccessFrameSp witness) - 80 + 32 =
        bv_unsigned (writeSuccessFrameSp witness) - 48 by lia.
    iEval (rewrite HstackHalf /=) in "HstackHigh32".
    iRename select (writeSuccessTerminalSavedSlots witness)%I into "Hterminal".
    iEval (rewrite /writeSuccessTerminalSavedSlots) in "Hterminal".
    iRename select (writeSuccessTransactionsInvariant _ _ _ _ _ _ _ _)%I
      into "HtxInvariant".
    iEval (rewrite /writeSuccessTransactionsInvariant) in "HtxInvariant".
    repeat iDestruct select (_ ∗ _)%I as "[? ?]".
    repeat iDestruct select (∃ _, _)%I as (?) "?".
    repeat iDestruct select (⌜_⌝)%I as %?.
    iFrame. iFrame "%".
  }
  iAssert (writeSuccessExactPostWithdrawalsCallerFrame args witness)%I
    with "[HcallerRaw]" as "Hcaller".
  { iApply (bi.equiv_entails_1_2 _ _ (writeSuccessExactPostWithdrawalsCallerFrame_unfold args witness)); iFrame. }
  have HbaseRoundtrip : Z_to_bv 64
      (bv_unsigned (writeSuccessWithdrawalsBase witness)) =
      writeSuccessWithdrawalsBase witness by bv_solve.
  have Hx8Value : Z_to_bv 64
      (bv_unsigned (writeSuccessWithdrawalsBase witness) + Z.of_nat 0) =
      writeSuccessWithdrawalsBase witness by
    rewrite /= Z.add_0_r HbaseRoundtrip.
  iDestruct (mem_mapsto_uninit_split 104 with "Hstack1640")
    as "[_ Hstack1744Tail]"; first lia.
  iDestruct (mem_mapsto_uninit_split 48 with "Hstack1744Tail")
    as "[Hstack1744 _]"; first lia.
  have Hstack1744Address : bv_unsigned (writeSuccessFrameSp witness) + 1640 + 104 =
      bv_unsigned (writeSuccessFrameSp witness) + 1744 by lia.
  iEval (rewrite Hstack1744Address) in "Hstack1744".
  iAssert (writeSuccessExactPostWithdrawalsUntouched
      (bv_unsigned (writeSuccessWithdrawalsBase witness)) []
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P))%I
    with "[Hcaller HP]" as "Huntouched".
  { iApply (bi.equiv_entails_1_2 _ _
      (writeSuccessExactPostWithdrawalsUntouched_unfold _ _ _)).
    rewrite mem_mapsto_array_eq /mem_mapsto_array_def /=.
    iSplitR "Hcaller HP".
    { iExists 1%N. iSplit; first done. iSplit; last done.
      iPureIntro.
      have Hr := bv_unsigned_in_range 64 (writeSuccessWithdrawalsBase witness).
      unfold bv_modulus in Hr. simpl in Hr. lia. }
    { iFrame. } }
  zesu_run.
  all: try zesu_open_matching_copied_word_package; zesu_run.
  all: try zesu_open_matching_resource_package; zesu_run.
  all: try (cbv [mapRamBase machineRamEnd mapRamSize defaultMap] in HstackLow, HstackHigh; lia).
  all: try assumption.
  all: rewrite ?Hx8Value.
  all: iFrame.
  all: rewrite big_sepL_nil.
  all: iFrame.
  all: iPureIntro; unfold writeSuccessWitnessWellFormed in Hwf; tauto.
Qed.

Lemma write_success_exact_withdrawals_zero
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  instr_body 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)) -∗
  instr_body 0x156e8
    (exactTailWithdrawalsBranchZeroEntry args witness P).
Proof.
  iStartProof. iIntros "Hpost".
  iApply (instr_pre_wand 0x156e8 0x156e8 false false with "Hpost");
    [done | reflexivity |].
  iIntros "Hentry".
  iApply (write_success_exact_withdrawals_zero_resources args witness P Hwf
    with "Hentry").
Qed.

Print Assumptions write_success_exact_withdrawals_zero.
