Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeCode WriteSuccessNativeContract
  WriteSuccessRepresentation WriteSuccessExactWithdrawalsHeadConnection
  WriteSuccessExactWithdrawalsLoopBody WriteSuccessExactWithdrawalsLoopClosed
  WriteSuccessExactWithdrawalsNativeRows WriteSuccessExactWithdrawalsZeroConnection
  WriteSuccessExactPostTransactionsSegment WriteSuccessExactTailRawLoadEntryAdapter
  ContractChainWithdrawalCode.

Lemma draft_tail_from_post_withdrawals
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)) -∗
  □ instr_pre 0x15668
    (writeSuccessExactTransactionsExitBoundary
      (writeSuccessFrameSp witness) (writeSuccessTransactionBase witness)
      (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness)
      (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P)).
Proof.
  iIntros "#Hcode #Hpost".
  iPoseProof (write_success_native_main_code with "Hcode") as "#HmainCode".
  iEval (rewrite /writeSuccessNativeMainCode) in "HmainCode".
  iDestruct "HmainCode" as "(#Hlookup & #Hspec & _)".
  iPoseProof (draft_withdrawal_loop_code_from_lookup with "Hlookup")
    as "#Hwithdrawals".
  iEval (unfold withdrawalLoopCode; rewrite !big_sepL_cons big_sepL_nil)
    in "Hwithdrawals".
  iDestruct "Hwithdrawals" as
    "#(H90 & H91 & H92 & H93 & H94 & H95 & Hcopy & Hint & Houtput & _)".
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
  iAssert (instr_body 0x15694
      (exactTailWithdrawalsBranchNonzeroEntry args witness P))%I
    with "[Hbody]" as "#HnonzeroBody".
  { iApply (instr_pre_wand 0x15694 0x15694 false false with "Hbody");
      [done | reflexivity |].
    iIntros "Hentry".
    iEval (rewrite /exactTailWithdrawalsBranchNonzeroEntry) in "Hentry".
    iDestruct "Hentry" as "[Hresources %Hpositive]".
    have [row [rest [Hrows Hfacts]]] :=
      write_success_exact_withdrawal_initial_facts args witness Hwf Hpositive.
    rewrite <- Hrows in Hfacts.
    iApply (write_success_exact_withdrawals_head_resources args witness P
      row rest Hwf Hrows Hfacts with "Hresources Hpost"). }
  iAssert (□ instr_pre 0x15694
      (exactTailWithdrawalsBranchNonzeroEntry args witness P))%I
    with "[]" as "#Hnonzero".
  { iModIntro. iApply instr_pre_to_body. iNext. iExact "HnonzeroBody". }
  iAssert (□ instr_pre 0x156e8
      (exactTailWithdrawalsBranchZeroEntry args witness P))%I
    with "[]" as "#Hzero".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (write_success_exact_withdrawals_zero args witness P Hwf).
    iApply instr_pre_to_body. iNext. iExact "Hpost". }
  iPoseProof (write_success_exact_post_transactions_segment
    args witness P Hwf with "Hcode Hnonzero Hzero") as "Hsegment".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand 0x15668 0x15668 false false with "Hsegment");
    [done | reflexivity |].
  iIntros "Hentry".
  iApply (exact_tail_raw_load_entry_adapter args witness P with "Hentry").
Qed.

Print Assumptions draft_tail_from_post_withdrawals.

(** The 0x1596c premise is the open tail-fields second segment.
    The 0x159b8 and 0x159d8 continuations use merged proofs. *)
