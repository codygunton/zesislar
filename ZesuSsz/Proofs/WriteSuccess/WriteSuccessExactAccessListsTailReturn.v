Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTailEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma access_tail_loop_return_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes x19 savedX22 data pointer tail (P : iProp Sigma) :
  accessListsTailPost sp (Z_to_bv 64 (Z.of_nat (length processed)))
    (accessTailLoopFrame sp base entries (processed ++ [entry]) rest bytes x19 savedX22
      data pointer tail P) -∗
  writeSuccessExactAccessListsState sp base entries (processed ++ [entry]) rest bytes
    (Z_to_bv 64 (Z.of_nat (length processed))) x19 savedX22 data pointer (BV 64 0) tail P.
Proof.
  iIntros "(Hsys & Hsp & H11 & Hindex & %Halign8 & %Hlow0 & %Hhigh0 & Hframe & _)".
  iDestruct "Hframe" as "(Hregs & H19 & Hdata & Hptr & Hcount & Hbytes & Hown & Hscratch &
    Hmmio & Htrace & Hpartition & Hencoding & Hlength & Htotalbound & Halign & Hlow & Hhigh &
    Hbaselow & Hbasehigh & HP & _)".
  iDestruct "Hscratch" as "(Hsaved & Hbase & Htotal & Hcopied & Hstack & Hkeyscratch & _)".
  have Hnext : (Z_to_bv 64 (Z.of_nat (length processed)) + BV 64 1)%bv =
      Z_to_bv 64 (Z.of_nat (length (processed ++ [entry]))).
  { rewrite app_length Nat2Z.inj_add /=. clear -processed. bv_solve. }
  iEval (rewrite Hnext) in "H11".
  unfold writeSuccessExactAccessListsState, writeSuccessAccessListsScratch. iFrame.
Qed.
Print Assumptions access_tail_loop_return_resources.
