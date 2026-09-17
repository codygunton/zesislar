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
  have [Hcount [Hall Hconcat]] := write_success_exact_withdrawal_rows_facts args witness Hwf.
  have [HstackLow HstackHigh] := exact_tail_stack_call_bounds args witness Hwf.
  iStartProof. iIntros "Hpost".
  iApply (instr_pre_wand 0x156e8 0x156e8 false false with "Hpost"); [done | reflexivity |].
  iIntros "Hentry".
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
  iEval (rewrite Hevents HbaseWord HcountWord HbytesNil) in "Hentry".
  iEval (rewrite /writeSuccessExactPostWithdrawalsBoundary /writeSuccessExactPostWithdrawalsCallerFrame
    /writeSuccessExactPostWithdrawalsMemoryFrame /writeSuccessExactValueMemory).
  iExists (BV 64 0x1568c). rewrite HbytesNil /=.
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  repeat iDestruct select (⌜_⌝)%I as %?.
  zesu_run.
  all: try zesu_open_matching_copied_word_package; zesu_run.
  all: try zesu_open_matching_resource_package; zesu_run.
  all: try (cbv [mapRamBase machineRamEnd mapRamSize defaultMap] in HstackLow, HstackHigh; lia).
  all: try assumption.
  all: iFrame.
  all: iPureIntro; unfold writeSuccessWitnessWellFormed in Hwf; tauto.
Qed.

Print Assumptions write_success_exact_withdrawals_zero.
