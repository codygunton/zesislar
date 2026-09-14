Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsTailBranches
  WriteSuccessExactWithdrawalsTailNative WriteSuccessExactWithdrawalsReturnFacts.
Lemma withdrawal_tail_positive `{!islaG Sigma} `{!threadG}
    sp pointer base rows prefix row rest source tail (P : iProp Sigma) :
  withdrawalTailHeadPost pointer (Z_to_bv 64 (Z.of_nat (S (length rest))))
    (withdrawalTailPayload sp pointer base rows prefix row rest source tail P) -∗
  withdrawalLoopSpec sp base rows source tail P.
Proof.
  rewrite /withdrawalTailHeadPost /withdrawalTailPost.
  iIntros "((Hsys & H8 & H9 & Hpayload & _) & %Hnonzero & _)".
  have Hdecrement : ((Z_to_bv 64 (Z.of_nat (S (length rest)))) - BV 64 1)%bv =
    Z_to_bv 64 (Z.of_nat (length rest)) by (rewrite Nat2Z.inj_succ; bv_solve).
  rewrite Hdecrement in Hnonzero. iEval (rewrite Hdecrement) in "H9".
  destruct rest as [|next rest].
  { exfalso. apply Hnonzero. apply bv_eq. reflexivity. }
  iDestruct "Hpayload" as "(Hsp & H1 & H5 & H18 & Hregs & Hsource & Hcopy & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  pose proof (withdrawal_facts_advance sp pointer base rows prefix row next rest source Hfacts) as HnewFacts.
  unfold withdrawalLoopSpec. iExists (prefix ++ [row]), next, rest,
    (pointer + BV 64 48)%bv, (BV 64 0x156dc), (BV 64 (mapIoContextAddress defaultMap)).
  unfold withdrawalLoopPayload. iFrame. done.
Qed.
Print Assumptions withdrawal_tail_positive.
