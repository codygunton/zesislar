Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawReadySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawReadyComposition.

Lemma exact_tail_raw_ready_pre `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15674 (exactTailRawReady args witness P) -∗
  □ instr_pre 0x15668
    (transactionLiveLoopExit (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness)
      (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P)).
Proof.
  iStartProof. iIntros "#Hnative #Hready".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (exact_tail_raw_ready args witness P Hwf with "Hnative Hready").
Qed.

Print Assumptions exact_tail_raw_ready_pre.
