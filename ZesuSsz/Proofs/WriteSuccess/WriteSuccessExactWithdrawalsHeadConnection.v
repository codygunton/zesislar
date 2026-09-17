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
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  repeat iDestruct select (⌜_⌝)%I as %?.
  iEval (rewrite /withdrawalLoopSpec /withdrawalLoopPayload
    /writeSuccessExactPostWithdrawalsCallerFrame
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
