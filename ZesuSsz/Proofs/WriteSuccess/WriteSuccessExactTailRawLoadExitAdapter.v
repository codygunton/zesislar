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

Lemma exact_tail_raw_load_exit_adapter `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  exactTailRawLoadExit (writeSuccessFrameSp witness) (writeSuccessValues witness)
    (writeSuccessExactTailEvents witness)
    (exactTailRawLoadMachineFrame args witness P) -∗
  exactTailRawReady args witness P.
Proof.
  rewrite /exactTailRawLoadExit /exactTailRawReady /exactTailRawLoadMachineFrame /exactTailRawLoadFrame
    /transactionLiveScratch /writeSuccessExactTailCallerWithCopiedWords.
  iIntros "(Hsys & Hregs & H1 & H2 & H10 & H11 & Hvalues & Htrace &
    (HscratchLower & HcallerLower & Hitems & Hmmio & Hbase & Hown &
    HbaseWord & HcountWord & HscratchMiddle & HscratchUpper & Hsp & Hcopied &
    Hsource & HcallerUpper & Hsaved & Hdecoded & Hpayload & Hwithdrawals &
    Hpost & Hstatic & Hinvariant & Hwf & HP & _) & _)".
  iFrame.
Qed.
Print Assumptions exact_tail_raw_load_exit_adapter.
