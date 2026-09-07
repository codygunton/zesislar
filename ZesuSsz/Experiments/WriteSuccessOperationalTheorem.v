From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import stdpp.base.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Contracts.ExecutionCertificate.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalDefinitions.

Import ListNotations.
Open Scope Z_scope.

Section PhaseBLedger.
  (** Each family variable supplies the Appendix A block postconditions. *)
  Variable phaseBBlockParams : Type.
  Variable phaseBInvariant :
    @Inv_ WriteSuccessConcreteState WriteSuccessExecutionArgs
      WriteSuccessBlock phaseBBlockParams.
  Variable phaseBEntryConsistent :
    WriteSuccessExecutionArgs -> WriteSuccessConcreteState -> Prop.
  Variable phaseBBlockLength : WriteSuccessBlock -> nat.
  Variable phaseBBlockSuccessor :
    WriteSuccessExecutionArgs -> WriteSuccessBlock -> phaseBBlockParams ->
    WriteSuccessConcreteState -> WriteSuccessConcreteState.
  Variable phaseBRank :
    WriteSuccessExecutionArgs -> WriteSuccessConcreteState -> nat.
  Variable phaseBBlockRecords :
    WriteSuccessExecutionArgs -> WriteSuccessBlock -> phaseBBlockParams ->
    nat -> list WriteSuccessRecord.
  Variable phaseBPrologue :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessPrologue.
  Variable phaseBHeader :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessHeader.
  Variable phaseBTransactions :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessTransactions.
  Variable phaseBAccessLists :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessAccessLists.
  Variable phaseBStorageKeys :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessStorageKeys.
  Variable phaseBBlobHashes :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessBlobHashes.
  Variable phaseBAuthorizations :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessAuthorizations.
  Variable phaseBPostTransactions :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessPostTransactions.
  Variable phaseBWithdrawals :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessWithdrawals.
  Variable phaseBPostWithdrawals :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessPostWithdrawals.
  Variable phaseBSuffixHashes :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessSuffixHashes.
  Variable phaseBTail :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessTail.
  Variable phaseBEpilogue :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEpilogue.
  Variable phaseBWriteOutput :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessWriteOutput.
  Variable phaseBMemcpy :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessMemcpy.
  Variable phaseBEncoderInt :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderInt.
  Variable phaseBEncoderBoolean :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderBoolean.
  Variable phaseBEncoderOptionalU64 :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderOptionalU64.
  Variable phaseBEncoderBytes :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderBytes.
  Variable phaseBEncoderByteLists :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderByteLists.

  Variable phaseBEntryBlock :
    forall args state,
      writeSuccessPairedEntry args state ->
      exists block params,
        phaseBInvariant args block params state /\
        phaseBEntryConsistent args state.
  Variable phaseBEntryRankBound :
    forall args state,
      writeSuccessPairedEntry args state ->
      (phaseBRank args state <= writeSuccessInstructionBoundConstant)%nat.
  Variable phaseBRoundTrip : writeSuccessObservationRoundTrip.

  Lemma phaseBBlockFamily block :
    WriteSuccessBlockFamily phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      block.
  Proof using All.
    destruct block; assumption.
  Qed.

  Lemma phaseBEntryBlockWithLength args state :
    writeSuccessPairedEntry args state ->
    exists block params,
      phaseBInvariant args block params state /\
      phaseBEntryConsistent args state /\
      (0 < phaseBBlockLength block)%nat.
  Proof using All.
    intros Hentry.
    destruct (phaseBEntryBlock args state Hentry)
      as (block & params & Hinvariant & Hconsistent).
    pose proof (phaseBBlockFamily block) as Hfamily.
    specialize (Hfamily args params state Hinvariant).
    exists block, params. tauto.
  Qed.

  Lemma phaseBDecreasingExecutionObligations :
    DecreasingExecutionObligations
      writeSuccessConcreteStep writeSuccessConcretePc writeSuccessPairedEntry
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs) 0x14d30
      (fun _ => writeSuccessInstructionBoundConstant).
  Proof using All.
    eapply decreasingExecutionObligationsFromBlocks with
      (blockInvariant := phaseBInvariant)
      (entryConsistent := phaseBEntryConsistent)
      (blockLength := phaseBBlockLength)
      (blockSuccessor := phaseBBlockSuccessor)
      (rank := phaseBRank).
    - intros [args initial] state (-> & Hentry).
      exact (writeSuccessConcreteEntryPc _ _ Hentry).
    - unfold PcInList. cbn [writeSuccessExitPcs].
      intros [Hequal | []]. discriminate Hequal.
    - exact phaseBEntryBlockWithLength.
    - intros args block params offset entryState Hinvariant Hoffset.
      pose proof (phaseBBlockFamily block) as Hfamily.
      destruct (Hfamily args params entryState Hinvariant)
        as (_ & Hoffsets & _).
      destruct (Hoffsets offset Hoffset)
        as (address & Hpc & _).
      eauto.
    - intros args block params offset entryState address
        Hinvariant Hoffset Hpc.
      pose proof (phaseBBlockFamily block) as Hfamily.
      destruct (Hfamily args params entryState Hinvariant)
        as (_ & Hoffsets & _).
      destruct (Hoffsets offset Hoffset)
        as (found & Hfound & _ & Hclassified).
      rewrite Hpc in Hfound. inversion Hfound. subst. exact Hclassified.
    - intros args block params offset entryState index
        Hinvariant Hoffset HnotExit.
      pose proof (phaseBBlockFamily block) as Hfamily.
      destruct (Hfamily args params entryState Hinvariant)
        as (_ & _ & Hprogress & _).
      exact (Hprogress offset index Hoffset HnotExit).
    - intros args block params offset entryState index after
        Hinvariant Hoffset Hstep.
      pose proof (phaseBBlockFamily block) as Hfamily.
      destruct (Hfamily args params entryState Hinvariant)
        as (_ & _ & _ & Hcovered & _).
      exact (Hcovered offset index after Hoffset Hstep).
    - intros args block params entryState Hinvariant.
      pose proof (phaseBBlockFamily block) as Hfamily.
      destruct (Hfamily args params entryState Hinvariant)
        as (_ & _ & _ & _ & _ & _ & Hhandoff).
      exact Hhandoff.
    - intros args block params offset entryState
        Hinvariant Hoffset HnotExit.
      pose proof (phaseBBlockFamily block) as Hfamily.
      destruct (Hfamily args params entryState Hinvariant)
        as (_ & _ & _ & _ & Hdecrease & _).
      exact (Hdecrease offset Hoffset HnotExit).
    - exact phaseBEntryRankBound.
  Qed.

  Lemma phaseBPairedExecutionCertificate :
    ExecutionPathCertificate
      writeSuccessConcreteStep writeSuccessConcretePc writeSuccessPairedEntry
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs) 0x14d30
      (fun _ => writeSuccessInstructionBoundConstant).
  Proof using All.
    exact (executionCertificateFromDecrease
      _ _ _ _ _ _ _ phaseBDecreasingExecutionObligations).
  Qed.

  Lemma phaseBExecutionCertificate :
    ExecutionPathCertificate
      writeSuccessConcreteStep writeSuccessConcretePc
      writeSuccessConcreteEntry
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs) 0x14d30
      (fun _ => writeSuccessInstructionBoundConstant).
  Proof using All.
    destruct phaseBPairedExecutionCertificate as
      [HentryPc Hterminal Hprefixes Hprogress Hmaximal HnoInfinite].
    constructor.
    - intros args before Hentry.
      exact (HentryPc (args, before) before (conj eq_refl Hentry)).
    - intros args fromStep before Hentry.
      exact (Hterminal (args, before) fromStep before
        (conj eq_refl Hentry)).
    - intros args fromStep count before after Hentry Htrace.
      exact (Hprefixes (args, before) fromStep count before after
        (conj eq_refl Hentry) Htrace).
    - intros args fromStep count before state Hentry Htrace HnotExit.
      exact (Hprogress (args, before) fromStep count before state
        (conj eq_refl Hentry) Htrace HnotExit).
    - intros args fromStep count before state Hentry Htrace Hstuck.
      exact (Hmaximal (args, before) fromStep count before state
        (conj eq_refl Hentry) Htrace Hstuck).
    - intros args fromStep before Hentry.
      exact (HnoInfinite (args, before) fromStep before
        (conj eq_refl Hentry)).
  Qed.

  Lemma phaseBTerminalInvariant args fromStep count before after :
    writeSuccessConcreteEntry args before ->
    StoppedTrace writeSuccessConcreteStep writeSuccessConcretePc
      (PcInList writeSuccessExitPcs) fromStep count before after ->
    blockExecutionInvariant phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor (args, before) after.
  Proof using All.
    intros Hentry Htrace.
    destruct (phaseBEntryBlockWithLength (args, before) before
      (conj eq_refl Hentry))
      as (block & params & Hinvariant & Hconsistent & Hlength).
    pose proof (blockExecutionInvariantAtEntry phaseBInvariant
      phaseBEntryConsistent phaseBBlockLength phaseBBlockSuccessor
      (args, before) block params before Hinvariant Hconsistent Hlength)
      as HblockEntry.
    eapply (stoppedTraceInvariant writeSuccessConcreteStep
      writeSuccessConcretePc (PcInList writeSuccessExitPcs)
      (blockExecutionInvariant phaseBInvariant phaseBEntryConsistent
        phaseBBlockLength phaseBBlockSuccessor)); try eassumption.
    eapply blockInvariantPreserved.
    - intros executionArgs currentBlock currentParams offset entryState
        index next Hcurrent Hoffset Hstep.
      pose proof (phaseBBlockFamily currentBlock) as Hfamily.
      destruct (Hfamily executionArgs currentParams entryState Hcurrent)
        as (_ & _ & _ & Hcovered & _).
      exact (Hcovered offset index next Hoffset Hstep).
    - intros executionArgs currentBlock currentParams entryState Hcurrent.
      pose proof (phaseBBlockFamily currentBlock) as Hfamily.
      destruct (Hfamily executionArgs currentParams entryState Hcurrent)
        as (_ & _ & _ & _ & _ & _ & Hhandoff).
      exact Hhandoff.
  Qed.

End PhaseBLedger.

Print Assumptions phaseBDecreasingExecutionObligations.
Print Assumptions phaseBPairedExecutionCertificate.
Print Assumptions phaseBExecutionCertificate.
Print Assumptions phaseBTerminalInvariant.
