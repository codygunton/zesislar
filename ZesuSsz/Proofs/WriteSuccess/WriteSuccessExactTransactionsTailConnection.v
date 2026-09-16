Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessNativeContract
  WriteSuccessRepresentation WriteSuccessExactTailRawReadySpec
  WriteSuccessExactTailRawReadyComposition.

Lemma write_success_exact_transactions_tail_connection
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15674 (exactTailRawReady args witness P) -∗
  □ instr_pre 0x15668
    (writeSuccessExactTransactionsExitBoundary
      (writeSuccessFrameSp witness) (writeSuccessTransactionBase witness)
      (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness)
      (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P)).
Proof.
  iIntros "#Hcode #Htail". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (exact_tail_raw_ready args witness P Hwf with "Hcode Htail").
Qed.

Print Assumptions write_success_exact_transactions_tail_connection.
