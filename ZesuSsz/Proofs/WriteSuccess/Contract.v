Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedPrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveOuterExport.

(** Phase 3.5 fixes the public target before the region proofs arrive.
    The final theorem must discharge this proposition without region premises.
    Transactions use the exact live boundaries exported by [Interfaces].
    The entry chain reaches 0x14f04. Transactions reach 0x15668.
    The tail chain returns [writeSuccessTerminalResources] at 0x14d10. *)
Definition writeSuccessContractTarget {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (nextPc : Z -> Z -> Prop) : Prop :=
  IslarisContractCorrect 0x14d30 0x14d10
    (writeSuccessNativeModel allows outputRelation nextPc).

(** The exact target preserves the caller trace and returned registers. *)
Definition writeSuccessFixedTailContractTarget {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (fixedTail : spec) (nextPc : Z -> Z -> Prop) : Prop :=
  IslarisContractCorrect 0x14d30 0x14d10
    (writeSuccessFixedTailModel allows outputRelation fixedTail nextPc).

(** The final contract proof supplies [Htail] from the seven exact tail
    segments.  This lemma composes that continuation with the transaction
    Löb closure and the exact copied prefix. *)
Lemma write_success_contract_from_tail `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15668
    (writeSuccessExactTransactionsExitBoundary
      (writeSuccessFrameSp witness) (writeSuccessTransactionBase witness)
      (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness)
      (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P)) -∗
  instr_body 0x14d30
    (write_success_prologue_entry
      (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
      (writeSuccessReturnValue witness)
      (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
      (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
      (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
      (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
      (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
      (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
      (writeSuccessProloguePayload witness ∗ P)).
Proof.
  iIntros "#Hcode #Htail".
  iPoseProof (transactions_live_complete_outer
    (writeSuccessFrameSp witness) (writeSuccessTransactionBase witness)
    (writeSuccessTransactions witness)
    (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
    (writeSuccessExactTailEvents witness)
    (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P)%I
    with "Hcode Htail") as "#Htransactions".
  iApply (write_success_exact_copied_prefix args witness P Hwf
    with "Hcode Htransactions").
Qed.

Print Assumptions write_success_contract_from_tail.
