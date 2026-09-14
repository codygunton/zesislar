Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces WriteSuccessNativeContract
 WriteSuccessRepresentation WriteSuccessExactHeaderCallerEquiv WriteSuccessExactValueLiveEntry
 WriteSuccessExactTransactionsLiveSpec.
Lemma exact_header_transaction_guard `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  □ instr_pre 0x14f04
    (writeSuccessExactTransactionsEntryBoundary (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness) []
      (writeSuccessTransactions witness) (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness) (writeSuccessExactTailCaller args witness ∗ P)) -∗
  □ instr_pre 0x14f04
    (transactionLiveLoopState (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness) []
      (writeSuccessTransactions witness) (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness)
      (writeSuccessExactValueLiveCaller (writeSuccessFrameSp witness) (writeSuccessValues witness)
        (writeSuccessPayload witness) (writeSuccessSourceBytes witness)
        (writeSuccessNativeStaticResources ∗ writeSuccessExactCallerRemainder args witness ∗ P))).
Proof.
  iIntros "#Hentry". iModIntro.
  iApply (instr_pre_wand 0x14f04 0x14f04 true true with "Hentry"); [done | reflexivity |].
  rewrite /writeSuccessExactTransactionsEntryBoundary.
  iIntros "Hstate".
  iEval (unfold transactionLiveLoopState) in "Hstate".
  iDestruct "Hstate" as "(Hsys & Hregs & H2 & H10 & H11 & Hbytes & Hown & Hscratch & Hmmio & Htrace & Hfacts & Hcaller & _)".
  iEval (rewrite -(write_success_exact_caller_equiv_framed args witness P)) in "Hcaller".
  rewrite /transactionLiveLoopState. iFrame.
Qed.
Print Assumptions exact_header_transaction_guard.
