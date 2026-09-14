Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeContract WriteSuccessEpilogueBlock.
Lemma write_success_exact_terminal_resources `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessEpiloguePost
    (writeSuccessFrameSp witness) (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
    (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
    (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
    (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
    (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessNativeExitMemory witness ∗ spec_trace (writeSuccessTraceTail witness)) -∗
  writeSuccessTerminalMachine witness ∗ writeSuccessNativeExitMemory witness ∗
  spec_trace (writeSuccessTraceTail witness).
Proof.
  have Hrestore : ((writeSuccessFrameSp witness) + BV 64 2000)%bv =
    writeSuccessEntrySp witness by rewrite /writeSuccessFrameSp; bv_solve.
  rewrite /writeSuccessEpiloguePost /writeSuccessEpilogueFrame.
  iIntros "(Hsys & H1 & Hother & H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hslots & Hterminal & _)".
  iDestruct "Hterminal" as "[Hmemory Htrace]".
  iEval (rewrite /writeSuccessEpilogueSavedSlots) in "Hslots".
  iDestruct "Hslots" as "(Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11)".
  rewrite /writeSuccessTerminalMachine /writeSuccessTerminalSavedSlots Hrestore.
  iFrame.
Qed.
Print Assumptions write_success_exact_terminal_resources.
