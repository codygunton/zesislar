Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsTailBranches
  WriteSuccessExactWithdrawalsTailNative WriteSuccessExactWithdrawalsReturnFacts.
Require Import ZesuSsz.Automation.CounterZero.
Lemma withdrawal_tail_zero `{!islaG Sigma} `{!threadG}
    sp pointer base rows prefix row rest source tail (P : iProp Sigma) :
  withdrawalTailExitPost pointer (Z_to_bv 64 (Z.of_nat (S (length rest))))
    (withdrawalTailPayload sp pointer base rows prefix row rest source tail P) -∗
  (withdrawalLoopExit sp base source tail P ∗
   instr_pre 0x156e8 (withdrawalLoopExit sp base source tail P) ∗ True)%I.
Proof.
  rewrite /withdrawalTailExitPost /withdrawalTailPost.
  iIntros "((Hsys & H8 & H9 & Hpayload & _) & %Hzero & _)".
  have Hdecrement : ((Z_to_bv 64 (Z.of_nat (S (length rest)))) - BV 64 1)%bv =
    Z_to_bv 64 (Z.of_nat (length rest)) by (rewrite Nat2Z.inj_succ; bv_solve).
  rewrite Hdecrement in Hzero. iEval (rewrite Hdecrement) in "H9".
  iDestruct "Hpayload" as "(Hsp & H1 & H5 & H18 & Hregs & Hsource & Hcopy & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  have Hbound : (Z.of_nat (length rest) < 18446744073709551616)%Z.
  { destruct Hfacts as (_ & _ & _ & _ & Hcount & _). rewrite Nat2Z.inj_succ in Hcount. lia. }
  have HrestZero := zesu_counter_zero_z_bound (length rest) Hbound Hzero.
  destruct rest as [|next rest]; last (cbn in HrestZero; lia).
  have HendPointer := withdrawal_facts_end_pointer sp pointer base rows prefix row source Hfacts.
  iEval (rewrite HendPointer) in "H8". iEval (rewrite Hzero) in "H9".
  iSplitL "Hsys Hsp H1 H5 H18 H8 H9 Hregs Hsource Hcopy Hscratch Hmmio Htrace HP".
  2: { iFrame. }
  unfold withdrawalLoopExit. iFrame.
Qed.
Print Assumptions withdrawal_tail_zero.
