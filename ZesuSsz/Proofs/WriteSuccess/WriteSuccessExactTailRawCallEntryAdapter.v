Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixByteListPayloadAtSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawReadySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallEntrySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawByteListsModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailByteListFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Open Scope Z_scope.
Lemma exact_tail_raw_ready_to_call `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) (Hwf : writeSuccessWitnessWellFormed args witness) :
  exactTailRawReady args witness P -∗ exactTailRawCallEntry args witness P.
Proof.
  have Hfacts : writeSuccessTransactionsPost15674ByteListFacts
    (writeSuccessFrameSp witness)
    (writeSuccessValueWord (writeSuccessValues witness) 9)
    (writeSuccessValueWord (writeSuccessValues witness) 10)
    (writeSuccessRawTransactions witness).
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  destruct Hfacts as (Hcount & HitemsLength & HpointerAlign & HpointerLower &
    HpointerUpper & HspExtract & HspLower & HspUpper).
  have [Hframe [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  rewrite /exactTailRawReady /writeSuccessExactTailCallerWithCopiedWords.
  iIntros "(Hsys & Hregs & H1 & H2 & H10 & H11 & Hbase & Hown & Hscratch &
    Hmmio & Htrace & (HcallerLower & Hsp & Hcopied & Hsource & Hvalues &
    HcallerUpper & Hsaved & Hdecoded & Hpayload & Hitems & Hwithdrawals &
    Hpost & Hstatic & Hinvariant & HwfResource & _) & HP & _)".
  iEval (unfold transactionLiveScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(HscratchLower & HbaseWord & HcountWord & HscratchMiddle & HscratchUpper & _)".
  iDestruct (exact_tail_byte_list_sizes with "Hitems") as "[%Hsizes Hitems]".
  iEval (rewrite /writeSuccessExactTailEvents
    (exact_tail_raw_byte_lists_model _ _ _ _ _ _ _ _ _ _ Hsizes)) in "Htrace".
  iAssert (exactTailRawCallMemoryFrame args witness P)%I with
    "[Hbase Hown HbaseWord HcountWord HscratchMiddle HscratchUpper Hsp Hcopied
      Hsource Hvalues HcallerUpper Hsaved Hdecoded Hpayload Hwithdrawals Hpost
      Hstatic Hinvariant HwfResource HP]" as "HmemoryFrame".
  { rewrite /exactTailRawCallMemoryFrame.
    iFrame "Hbase Hown HbaseWord HcountWord HscratchMiddle HscratchUpper Hsp
      Hcopied Hsource Hvalues HcallerUpper Hsaved Hdecoded Hpayload Hwithdrawals
      Hpost Hstatic Hinvariant HwfResource HP". }
  iStartProof. zesu_open_resource_groups. zesu_open_bits_registers.
  rewrite /exactTailRawCallEntry /exactSuffixByteListEntryAt
    /exactTailRawCallFrame.
  zesu_run.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions exact_tail_raw_ready_to_call.
