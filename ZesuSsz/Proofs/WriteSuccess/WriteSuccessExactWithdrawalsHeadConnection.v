Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessExactWithdrawalsLoopBody
  WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactTailStackCallBounds WriteSuccessExactTailWithdrawalCountSpec
  WriteSuccessExactTailWithdrawalLoadSpec
  WriteSuccessExactTailWithdrawalsBranchSpec
  WriteSuccessExactWithdrawalsInitial
  WriteSuccessExactWithdrawalsLoopClosed WriteSuccessExactWithdrawalsNativeConnection
  WriteSuccessExactWithdrawalsNativeRows WriteSuccessExactWithdrawalsPublic
  WriteSuccessExactValueSpec WriteSuccessValueSpec
  WriteSuccessNativeContract
  WriteSuccessRepresentation.

Lemma write_success_exact_withdrawals_head_resources
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (row : list (bv 8)) (rest : list (list (bv 8)))
    (Hwf : writeSuccessWitnessWellFormed args witness)
    (Hrows : writeSuccessExactWithdrawalRows witness = row :: rest)
    (Hfacts : withdrawalLoopFacts (writeSuccessFrameSp witness)
      (Z_to_bv 64 (bv_unsigned (writeSuccessWithdrawalsBase witness)))
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessExactWithdrawalRows witness) [] row rest
      (writeSuccessWithdrawalsBytes witness)) :
  exactTailWithdrawalBranchResources args witness P -∗
  instr_pre 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)) -∗
  withdrawalLoopSpec (writeSuccessFrameSp witness)
    (bv_unsigned (writeSuccessWithdrawalsBase witness))
    (writeSuccessExactWithdrawalRows witness)
    (writeSuccessWithdrawalsBytes witness)
    (writeSuccessExactPostWithdrawalsEvents witness)
    (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P).
Proof.
  have [HstackLow HstackHigh] := exact_tail_stack_call_bounds args witness Hwf.
  have [Hcount _] := write_success_exact_withdrawal_rows_facts args witness Hwf.
  rewrite Hrows /= in Hcount. symmetry in Hcount.
  have Htail := exact_tail_after_withdrawal_count_rows args witness Hwf.
  rewrite Hrows in Htail.
  have HbaseRoundtrip : Z_to_bv 64
      (bv_unsigned (writeSuccessWithdrawalsBase witness)) =
      writeSuccessWithdrawalsBase witness by bv_solve.
  rewrite HbaseRoundtrip in Hfacts.
  have HbaseWord : writeSuccessValueWord (writeSuccessValues witness) 11 =
      writeSuccessWithdrawalsBase witness by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  have HcountWord : writeSuccessValueWord (writeSuccessValues witness) 12 =
      Z_to_bv 64 (Z.of_nat (writeSuccessWithdrawalsCount witness)) by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  iStartProof. iIntros "Hresources HpostPre".
  iEval (rewrite /exactTailWithdrawalBranchResources /encoderIntExactFramedPost
    /exactTailWithdrawalBranchFrame /exactTailWithdrawalCommonFrame
    /exactTailWithdrawalValueRemainder /writeSuccessExactCopiedTailWords
    /WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources
    /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
    /WriteSuccessPostTransactionResources.writeSuccessHashesResources
    /WriteSuccessPostTransactionResources.writeSuccessOptionalDescriptorResources)
    in "Hresources".
  iEval (rewrite
    /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
    /WriteSuccessPostTransactionResources.writeSuccessHashesResources
    /WriteSuccessPostTransactionResources.writeSuccessOptionalDescriptorResources)
    in "Hresources".
  iDestruct "Hresources" as "[Hresources Hx18]".
  iDestruct "Hresources" as
    "[Hsys [Hx1 [Hx2 [Hx5 [Hx10 [Hx11 [HcallStack [Hmmio [Htrace [Hresources _]]]]]]]]]]".
  iDestruct "Hresources" as
    "[HcallerRegs1 [HcallerRegs2 [HcallerRegs3 Hresources]]]".
  iDestruct "Hresources" as "[Hx8 [Hx9 Hresources]]".
  repeat iDestruct "Hresources" as "[? Hresources]".
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
    with "[-HpostPre Hsys Hx1 Hx2 Hx5 Hx10 Hx11 HcallStack Hmmio Htrace Hx18
      Hx8 Hx9 HP Hstack1640 Hx12 Hx13 Hx14 Hx15
      HcallerRegs1 HcallerRegs2 HcallerRegs3 HstackHigh32]"
    as "HtailCaller".
  { iApply (bi.equiv_entails_1_2 _ _
      (writeSuccessExactTailCallerBundle_unfold args witness)).
    rewrite /writeSuccessExactTailCallerWithCopiedWords
      /writeSuccessExactCopiedTailWords /writeSuccessExactValueMemory
      /WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources
      /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
      /WriteSuccessPostTransactionResources.writeSuccessHashesResources
      /WriteSuccessPostTransactionResources.writeSuccessOptionalDescriptorResources.
    repeat first [zesu_open_matching_copied_word_package |
      zesu_open_matching_resource_package].
    iFrame. iFrame "%". }
  iEval (rewrite writeSuccessExactTailCallerBundle_unfold
    /writeSuccessExactTailCallerWithCopiedWords) in "HtailCaller".
  iDestruct "HtailCaller" as
    "[HtailStackLow [HtailSp [Hcopied HtailCaller]]]".
  iAssert (((bv_unsigned (writeSuccessFrameSp witness) + 72) ↦ₘ
      WriteSuccessPostTransactionResources.writeSuccessPostWord
        (WriteSuccessPostTransactionResources.writeSuccessPostTailWords
          (writeSuccessDecodedBytes witness)) 7) ∗
      writeSuccessExactCopiedTailWordsWithout7
        (writeSuccessFrameSp witness) (writeSuccessDecodedBytes witness))%I
    with "[Hcopied]" as "[Hword7 HcopiedRest]".
  { iEval (rewrite /writeSuccessExactCopiedTailWords) in "Hcopied".
    rewrite /writeSuccessExactCopiedTailWordsWithout7.
    repeat iDestruct "Hcopied" as "[? Hcopied]". iFrame. }
  iAssert ((writeSuccessExactPostWithdrawalsCallerFrameRestRaw args witness) ∗
      bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗
        writeSuccessWithdrawalsBytes witness)%I
    with "[HtailStackLow HtailSp HcopiedRest HtailCaller
      HcallerRegs1 HcallerRegs2 HcallerRegs3 HstackHigh32]"
    as "[HcallerRestRaw Hwithdrawals]".
  {
    repeat iDestruct "HtailCaller" as "[? HtailCaller]".
    iDestruct select (bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗
      writeSuccessWithdrawalsBytes witness)%I as "Hwithdrawals".
    iSplitR "Hwithdrawals"; last iFrame.
    iEval (rewrite /reg_col) in "HcallerRegs1 HcallerRegs2 HcallerRegs3".
    rewrite /writeSuccessExactPostWithdrawalsCallerFrameRestRaw
      /writeSuccessExactPostWithdrawalsMemoryFrame /writeSuccessExactValueMemory
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
    iFrame. iFrame "%". }
  iAssert (writeSuccessExactPostWithdrawalsCallerFrameRaw args witness)%I
    with "[Hword7 HcallerRestRaw]" as "HcallerRaw".
  { rewrite /writeSuccessExactPostWithdrawalsCallerFrameRaw. iFrame. }
  iAssert (writeSuccessExactPostWithdrawalsCallerFrame args witness)%I
    with "[HcallerRaw]" as "Hcaller".
  { iApply (bi.equiv_entails_1_2 _ _
      (writeSuccessExactPostWithdrawalsCallerFrame_unfold args witness)).
    iFrame. }
  iDestruct (mem_mapsto_uninit_split 104 with "Hstack1640")
    as "[_ Hstack1744Tail]"; first lia.
  iDestruct (mem_mapsto_uninit_split 48 with "Hstack1744Tail")
    as "[Hstack1744 _]"; first lia.
  have Hstack1744Address : bv_unsigned (writeSuccessFrameSp witness) + 1640 + 104 =
      bv_unsigned (writeSuccessFrameSp witness) + 1744 by lia.
  iEval (rewrite Hstack1744Address) in "Hstack1744".
  iAssert (instr_pre 0x156e8
      (withdrawalLoopExit (writeSuccessFrameSp witness)
        (bv_unsigned (writeSuccessWithdrawalsBase witness))
        (writeSuccessWithdrawalsBytes witness)
        (writeSuccessExactPostWithdrawalsEvents witness)
        (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)))%I
    with "[HpostPre]" as "HloopExit".
  { iApply (instr_pre_wand 0x156e8 0x156e8 true true with "HpostPre");
      [done | reflexivity |].
    iIntros "Hexit".
    rewrite /withdrawalLoopExit /writeSuccessExactPostWithdrawalsBoundary
      /writeSuccessExactPostWithdrawalsRegisters
      writeSuccessExactPostWithdrawalsUntouched_unfold /reg_col.
    repeat iDestruct select (_ ∗ _)%I as "[? ?]".
    repeat iDestruct select (∃ _, _)%I as (?) "?".
    repeat iDestruct select (⌜_⌝)%I as %?.
    simpl. iFrame. iPureIntro. done. }
  iEval (rewrite /withdrawalLoopSpec /withdrawalLoopPayload
    /writeSuccessExactPostWithdrawalsMemoryFrame /writeSuccessExactValueMemory).
  rewrite HbaseWord HcountWord Hcount Htail.
  iExists [], row, rest,
    (Z_to_bv 64 (bv_unsigned (writeSuccessWithdrawalsBase witness))),
    (BV 64 0x1568c), (BV 64 (mapIoContextAddress defaultMap)).
  zesu_run.
  all: try zesu_open_matching_copied_word_package; zesu_run.
  all: try zesu_open_matching_resource_package; zesu_run.
  all: try (cbv [mapRamBase machineRamEnd mapRamSize defaultMap]
    in HstackLow, HstackHigh; lia).
  all: try assumption.
  all: iFrame.
  all: rewrite big_sepL_nil.
  all: iFrame.
  all: iPureIntro; try exact Hfacts.
  all: unfold writeSuccessWitnessWellFormed in Hwf.
  all: split; [tauto | exact Hfacts].
Qed.

Lemma write_success_exact_withdrawals_head_connection
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  withdrawalLoopCode -∗
  instr_body 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)) -∗
  instr_body 0x15694 (exactTailWithdrawalsBranchNonzeroEntry args witness P).
Proof.
  iStartProof. iIntros "#Hcode Hpost".
  iEval (unfold withdrawalLoopCode; rewrite !big_sepL_cons big_sepL_nil) in "Hcode".
  iDestruct "Hcode" as "#(H90 & H91 & H92 & H93 & H94 & H95 & Hcopy & Hint & Houtput & _)".
  iPoseProof (withdrawal_loop_closed (writeSuccessFrameSp witness)
    (bv_unsigned (writeSuccessWithdrawalsBase witness))
    (writeSuccessExactWithdrawalRows witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessExactPostWithdrawalsEvents witness)
    (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P) with
    "H90 H91 H92 H93 H94 H95 Hcopy Hint Houtput") as "#Hloop".
  iPoseProof (withdrawal_loop_body (writeSuccessFrameSp witness)
    (bv_unsigned (writeSuccessWithdrawalsBase witness))
    (writeSuccessExactWithdrawalRows witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessExactPostWithdrawalsEvents witness)
    (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P) with
    "H90 H91 H92 H93 H94 H95 Hcopy Hint Houtput Hloop") as "Hbody".
  iApply (instr_pre_wand 0x15694 0x15694 false false with "Hbody");
    [done | reflexivity |].
  iIntros "Hentry".
  iEval (rewrite /exactTailWithdrawalsBranchNonzeroEntry) in "Hentry".
  iDestruct "Hentry" as "[Hresources %Hpositive]".
  have [row [rest [Hrows Hfacts]]] :=
    write_success_exact_withdrawal_initial_facts args witness Hwf Hpositive.
  rewrite <- Hrows in Hfacts.
  iAssert (instr_pre 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)))%I
    with "[Hpost]" as "HpostPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hpost". }
  iApply (write_success_exact_withdrawals_head_resources args witness P
    row rest Hwf Hrows Hfacts with "Hresources HpostPre").
Qed.

Print Assumptions write_success_exact_withdrawals_head_connection.
