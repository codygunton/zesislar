Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsTail
  WriteSuccessExactAuthorizationsReturnFacts.

Lemma authorization_tail_positive `{!islaG Sigma} `{!threadG}
    sp pointer base rows prefix row rest source tail (P : iProp Sigma) :
  (authorizationTailState (pointer + BV 64 144)%bv
    (Z_to_bv 64 (Z.of_nat (S (length rest))) - BV 64 1)%bv
    (authorizationTailPayload sp pointer base rows prefix row rest source tail P) ∗
   ⌜(Z_to_bv 64 (Z.of_nat (S (length rest))) - BV 64 1)%bv <> BV 64 0⌝ ∗ True)%I -∗
  authorizationLoopSpec sp base rows source tail P.
Proof.
  iIntros "(Hstate & %Hnonzero & _)".
  have Hdecrement : (Z_to_bv 64 (Z.of_nat (S (length rest))) - BV 64 1)%bv =
    Z_to_bv 64 (Z.of_nat (length rest)) by (rewrite Nat2Z.inj_succ; bv_solve).
  rewrite Hdecrement in Hnonzero. iEval (rewrite Hdecrement) in "Hstate".
  destruct rest as [|next rest].
  { exfalso. apply Hnonzero. apply bv_eq. reflexivity. }
  iDestruct "Hstate" as "(Hsys & H9 & H18 & Hpayload & _)".
  iDestruct "Hpayload" as "(Hsp & H1 & H5 & H8 & Hregs & Hsource & Hcopy & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  pose proof (authorization_facts_advance sp pointer base rows prefix row next rest source Hfacts) as HnewFacts.
  unfold authorizationLoopSpec. iExists (prefix ++ [row]), next, rest,
    (pointer + BV 64 144)%bv, (BV 64 0x15614), (BV 64 0x2401a0b8).
  unfold authorizationLoopPayload. iFrame. done.
Qed.
Print Assumptions authorization_tail_positive.
