Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From IslaTraces.write_success_89 Require Import instrs.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces
  WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactTailWithdrawalCountSpec WriteSuccessExactTailWithdrawalLoadSpec
  WriteSuccessExactTailWithdrawalsBranchSpec WriteSuccessExactTailStackCallBounds
  WriteSuccessExactWithdrawalsInitial WriteSuccessExactWithdrawalsNativeRows
  WriteSuccessExactWithdrawalsPublic
  WriteSuccessExactValueSpec WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessValueSpec.

Lemma write_success_exact_withdrawals_nonzero
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  ([∗ list] instruction ∈ IslaTraces.write_success_89.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  withdrawalLoopCode -∗
  instr_body 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)) -∗
  instr_body 0x1568c
    (exactTailWithdrawalsBranchNonzeroEntry args witness P).
Proof.
  have [HstackLow HstackHigh] := exact_tail_stack_call_bounds args witness Hwf.
  have HbaseWord : writeSuccessValueWord (writeSuccessValues witness) 11 =
      writeSuccessWithdrawalsBase witness by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  have HcountWord : writeSuccessValueWord (writeSuccessValues witness) 12 =
      Z_to_bv 64 (Z.of_nat (writeSuccessWithdrawalsCount witness)) by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  have HbaseRoundtrip : Z_to_bv 64
      (bv_unsigned (writeSuccessWithdrawalsBase witness)) =
      writeSuccessWithdrawalsBase witness by bv_solve.
  iStartProof. iIntros "#H89 #Hloop Hpost".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /exactTailWithdrawalsBranchNonzeroEntry) in "Hentry".
  iDestruct "Hentry" as "[Hresources %Hpositive]".
  have [row [rest [Hrows Hfacts]]] :=
    write_success_exact_withdrawal_initial_facts args witness Hwf Hpositive.
  have HrowCount : writeSuccessWithdrawalsCount witness = S (length rest).
  { have [Hcount _] := write_success_exact_withdrawal_rows_facts args witness Hwf.
    rewrite Hrows /= in Hcount. lia. }
  have Htail := exact_tail_after_withdrawal_count_rows args witness Hwf.
  rewrite Hrows in Htail.
  iAssert (instr_pre 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)))%I
    with "[Hpost]" as "HpostPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hpost". }
  iPoseProof (withdrawal_initial_closed (writeSuccessFrameSp witness)
    (BV 64 0x1568c) (BV 64 (mapIoContextAddress defaultMap))
    (bv_unsigned (writeSuccessWithdrawalsBase witness)) row rest
    (writeSuccessWithdrawalsBytes witness)
    (writeSuccessExactPostWithdrawalsEvents witness)
    (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)
    Hfacts with "H89 Hloop") as "Hclosed".
  iEval (rewrite instr_pre'_eq) in "Hclosed".
  iApply "Hclosed".
  iEval (rewrite /exactTailWithdrawalBranchResources
    /encoderIntExactFramedPost /exactTailWithdrawalBranchFrame
    /exactTailWithdrawalCommonFrame /exactTailWithdrawalValueRemainder
    /writeSuccessExactCopiedTailWords
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
  iEval (rewrite /withdrawalInitialEntry
    /writeSuccessExactPostWithdrawalsCallerFrame
    /writeSuccessExactPostWithdrawalsMemoryFrame /writeSuccessExactValueMemory).
  rewrite HbaseWord HbaseRoundtrip HcountWord HrowCount Htail.
  zesu_run.
  all: try zesu_open_matching_copied_word_package; zesu_run.
  all: try zesu_open_matching_resource_package; zesu_run.
  all: try (cbv [mapRamBase machineRamEnd mapRamSize defaultMap]
    in HstackLow, HstackHigh; lia).
  all: try assumption.
  all: iFrame.
  all: iPureIntro; unfold writeSuccessWitnessWellFormed in Hwf; tauto.
Qed.

Print Assumptions write_success_exact_withdrawals_nonzero.
