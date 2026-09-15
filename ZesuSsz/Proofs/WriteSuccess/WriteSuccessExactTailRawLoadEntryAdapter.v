Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawReadySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Open Scope Z_scope.

Lemma exact_tail_raw_load_entry_adapter `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  transactionLiveLoopExit (writeSuccessFrameSp witness)
    (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
    (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
    (writeSuccessExactTailEvents witness)
    (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P) -∗
  exactTailRawLoadEntry (writeSuccessFrameSp witness) (writeSuccessValues witness)
    (length (writeSuccessTransactions witness)) (writeSuccessExactTailEvents witness)
    (exactTailRawLoadMachineFrame args witness P).
Proof.
  rewrite /transactionLiveLoopExit /transactionLiveScratch
    /writeSuccessExactTailCallerWithCopiedWords /exactTailRawLoadEntry
    /exactTailRawLoadMachineFrame /exactTailRawLoadFrame.
  iIntros "(Hsys & Hregs & H2 & H10 & H11 & Hbase & Hown &
    (HscratchLower & HbaseWord & HcountWord & HscratchMiddle & HscratchUpper & _) &
    Hmmio & Htrace & ((HcallerLower & Hsp & Hcopied & Hsource & Hvalues &
    HcallerUpper & Hsaved & Hdecoded & Hpayload & Hitems & Hwithdrawals &
    Hpost & Hstatic & Hinvariant & Hwf & _) & HP) & _)".
  iFrame.
Qed.
Print Assumptions exact_tail_raw_load_entry_adapter.
