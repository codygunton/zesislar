Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsTail
  WriteSuccessExactAuthorizationsReturnFacts.

Lemma authorization_tail_zero `{!islaG Sigma} `{!threadG}
    sp pointer base rows prefix row rest source tail (P : iProp Sigma) :
  (authorizationTailState (pointer + BV 64 144)%bv
    (Z_to_bv 64 (Z.of_nat (S (length rest))) - BV 64 1)%bv
    (authorizationTailPayload sp pointer base rows prefix row rest source tail P) ∗
   ⌜(Z_to_bv 64 (Z.of_nat (S (length rest))) - BV 64 1)%bv = BV 64 0⌝ ∗ True)%I -∗
  (authorizationLoopExit sp base source tail P ∗
   instr_pre 0x15620 (authorizationLoopExit sp base source tail P) ∗ True)%I.
Proof.
  iIntros "(Hstate & %Hzero & _)".
  have Hdecrement : (Z_to_bv 64 (Z.of_nat (S (length rest))) - BV 64 1)%bv =
    Z_to_bv 64 (Z.of_nat (length rest)) by (rewrite Nat2Z.inj_succ; bv_solve).
  rewrite Hdecrement in Hzero. iEval (rewrite Hdecrement) in "Hstate".
  iDestruct "Hstate" as "(Hsys & H9 & H18 & Hpayload & _)".
  iDestruct "Hpayload" as "(Hsp & H1 & H5 & H8 & Hregs & Hsource & Hcopy & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  have Hbound : (Z.of_nat (length rest) < 18446744073709551616)%Z.
  { destruct Hfacts as (_ & _ & _ & _ & Hcount & _). rewrite Nat2Z.inj_succ in Hcount. lia. }
  have HrestZero := zesu_counter_zero_z_bound (length rest) Hbound Hzero.
  destruct rest as [|next rest]; last (cbn in HrestZero; lia).
  have HendPointer := authorization_facts_end_pointer sp pointer base rows prefix row source Hfacts.
  iEval (rewrite HendPointer) in "H9".
  iEval (rewrite Hzero) in "H18".
  iSplitL "Hsys Hsp H1 H5 H8 H9 H18 Hregs Hsource Hcopy Hscratch Hmmio Htrace HP".
  2: { iFrame. }
  unfold authorizationLoopExit. iFrame.
Qed.
Print Assumptions authorization_tail_zero.
