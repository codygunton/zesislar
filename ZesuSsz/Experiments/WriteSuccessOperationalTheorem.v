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
  Variable phaseBPrologueParams : Type.
  Variable phaseBPrologueInvariant :
    WriteSuccessExecutionArgs -> phaseBPrologueParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBHeaderParams : Type.
  Variable phaseBHeaderInvariant :
    WriteSuccessExecutionArgs -> phaseBHeaderParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBTransactionsParams : Type.
  Variable phaseBTransactionsInvariant :
    WriteSuccessExecutionArgs -> phaseBTransactionsParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBAccessListsParams : Type.
  Variable phaseBAccessListsInvariant :
    WriteSuccessExecutionArgs -> phaseBAccessListsParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBStorageKeysParams : Type.
  Variable phaseBStorageKeysInvariant :
    WriteSuccessExecutionArgs -> phaseBStorageKeysParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBBlobHashesParams : Type.
  Variable phaseBBlobHashesInvariant :
    WriteSuccessExecutionArgs -> phaseBBlobHashesParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBAuthorizationsParams : Type.
  Variable phaseBAuthorizationsInvariant :
    WriteSuccessExecutionArgs -> phaseBAuthorizationsParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBPostTransactionsParams : Type.
  Variable phaseBPostTransactionsInvariant :
    WriteSuccessExecutionArgs -> phaseBPostTransactionsParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBWithdrawalsParams : Type.
  Variable phaseBWithdrawalsInvariant :
    WriteSuccessExecutionArgs -> phaseBWithdrawalsParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBPostWithdrawalsParams : Type.
  Variable phaseBPostWithdrawalsInvariant :
    WriteSuccessExecutionArgs -> phaseBPostWithdrawalsParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBSuffixHashesParams : Type.
  Variable phaseBSuffixHashesInvariant :
    WriteSuccessExecutionArgs -> phaseBSuffixHashesParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBTailParams : Type.
  Variable phaseBTailInvariant :
    WriteSuccessExecutionArgs -> phaseBTailParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBEpilogueParams : Type.
  Variable phaseBEpilogueInvariant :
    WriteSuccessExecutionArgs -> phaseBEpilogueParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBWriteOutputParams : Type.
  Variable phaseBWriteOutputInvariant :
    WriteSuccessExecutionArgs -> phaseBWriteOutputParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBMemcpyParams : Type.
  Variable phaseBMemcpyInvariant :
    WriteSuccessExecutionArgs -> phaseBMemcpyParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBEncoderIntParams : Type.
  Variable phaseBEncoderIntInvariant :
    WriteSuccessExecutionArgs -> phaseBEncoderIntParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBEncoderBooleanParams : Type.
  Variable phaseBEncoderBooleanInvariant :
    WriteSuccessExecutionArgs -> phaseBEncoderBooleanParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBEncoderOptionalU64Params : Type.
  Variable phaseBEncoderOptionalU64Invariant :
    WriteSuccessExecutionArgs -> phaseBEncoderOptionalU64Params ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBEncoderBytesParams : Type.
  Variable phaseBEncoderBytesInvariant :
    WriteSuccessExecutionArgs -> phaseBEncoderBytesParams ->
    WriteSuccessConcreteState -> Prop.
  Variable phaseBEncoderByteListsParams : Type.
  Variable phaseBEncoderByteListsInvariant :
    WriteSuccessExecutionArgs -> phaseBEncoderByteListsParams ->
    WriteSuccessConcreteState -> Prop.

  Inductive phaseBBlockParams : Type :=
  | PhaseBPrologueParams : phaseBPrologueParams -> phaseBBlockParams
  | PhaseBHeaderParams : phaseBHeaderParams -> phaseBBlockParams
  | PhaseBTransactionsParams : phaseBTransactionsParams -> phaseBBlockParams
  | PhaseBAccessListsParams : phaseBAccessListsParams -> phaseBBlockParams
  | PhaseBStorageKeysParams : phaseBStorageKeysParams -> phaseBBlockParams
  | PhaseBBlobHashesParams : phaseBBlobHashesParams -> phaseBBlockParams
  | PhaseBAuthorizationsParams : phaseBAuthorizationsParams -> phaseBBlockParams
  | PhaseBPostTransactionsParams : phaseBPostTransactionsParams -> phaseBBlockParams
  | PhaseBWithdrawalsParams : phaseBWithdrawalsParams -> phaseBBlockParams
  | PhaseBPostWithdrawalsParams : phaseBPostWithdrawalsParams -> phaseBBlockParams
  | PhaseBSuffixHashesParams : phaseBSuffixHashesParams -> phaseBBlockParams
  | PhaseBTailParams : phaseBTailParams -> phaseBBlockParams
  | PhaseBEpilogueParams : phaseBEpilogueParams -> phaseBBlockParams
  | PhaseBWriteOutputParams : phaseBWriteOutputParams -> phaseBBlockParams
  | PhaseBMemcpyParams : phaseBMemcpyParams -> phaseBBlockParams
  | PhaseBEncoderIntParams : phaseBEncoderIntParams -> phaseBBlockParams
  | PhaseBEncoderBooleanParams : phaseBEncoderBooleanParams -> phaseBBlockParams
  | PhaseBEncoderOptionalU64Params : phaseBEncoderOptionalU64Params -> phaseBBlockParams
  | PhaseBEncoderBytesParams : phaseBEncoderBytesParams -> phaseBBlockParams
  | PhaseBEncoderByteListsParams : phaseBEncoderByteListsParams -> phaseBBlockParams.

  Definition phaseBInvariant :
      @Inv_ WriteSuccessConcreteState WriteSuccessExecutionArgs
        WriteSuccessBlock phaseBBlockParams :=
    fun args block params state =>
      match block, params with
      | WriteSuccessPrologue, PhaseBPrologueParams concreteParams =>
          phaseBPrologueInvariant args concreteParams state
      | WriteSuccessHeader, PhaseBHeaderParams concreteParams =>
          phaseBHeaderInvariant args concreteParams state
      | WriteSuccessTransactions, PhaseBTransactionsParams concreteParams =>
          phaseBTransactionsInvariant args concreteParams state
      | WriteSuccessAccessLists, PhaseBAccessListsParams concreteParams =>
          phaseBAccessListsInvariant args concreteParams state
      | WriteSuccessStorageKeys, PhaseBStorageKeysParams concreteParams =>
          phaseBStorageKeysInvariant args concreteParams state
      | WriteSuccessBlobHashes, PhaseBBlobHashesParams concreteParams =>
          phaseBBlobHashesInvariant args concreteParams state
      | WriteSuccessAuthorizations, PhaseBAuthorizationsParams concreteParams =>
          phaseBAuthorizationsInvariant args concreteParams state
      | WriteSuccessPostTransactions, PhaseBPostTransactionsParams concreteParams =>
          phaseBPostTransactionsInvariant args concreteParams state
      | WriteSuccessWithdrawals, PhaseBWithdrawalsParams concreteParams =>
          phaseBWithdrawalsInvariant args concreteParams state
      | WriteSuccessPostWithdrawals, PhaseBPostWithdrawalsParams concreteParams =>
          phaseBPostWithdrawalsInvariant args concreteParams state
      | WriteSuccessSuffixHashes, PhaseBSuffixHashesParams concreteParams =>
          phaseBSuffixHashesInvariant args concreteParams state
      | WriteSuccessTail, PhaseBTailParams concreteParams =>
          phaseBTailInvariant args concreteParams state
      | WriteSuccessEpilogue, PhaseBEpilogueParams concreteParams =>
          phaseBEpilogueInvariant args concreteParams state
      | WriteSuccessWriteOutput, PhaseBWriteOutputParams concreteParams =>
          phaseBWriteOutputInvariant args concreteParams state
      | WriteSuccessMemcpy, PhaseBMemcpyParams concreteParams =>
          phaseBMemcpyInvariant args concreteParams state
      | WriteSuccessEncoderInt, PhaseBEncoderIntParams concreteParams =>
          phaseBEncoderIntInvariant args concreteParams state
      | WriteSuccessEncoderBoolean, PhaseBEncoderBooleanParams concreteParams =>
          phaseBEncoderBooleanInvariant args concreteParams state
      | WriteSuccessEncoderOptionalU64, PhaseBEncoderOptionalU64Params concreteParams =>
          phaseBEncoderOptionalU64Invariant args concreteParams state
      | WriteSuccessEncoderBytes, PhaseBEncoderBytesParams concreteParams =>
          phaseBEncoderBytesInvariant args concreteParams state
      | WriteSuccessEncoderByteLists, PhaseBEncoderByteListsParams concreteParams =>
          phaseBEncoderByteListsInvariant args concreteParams state
      | _, _ => False
      end.
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

  Lemma phaseBInvariantTraceConfined executionArgs fromStep count before after :
    blockExecutionInvariant phaseBInvariant phaseBEntryConsistent
      phaseBBlockLength phaseBBlockSuccessor executionArgs before ->
    StoppedTrace writeSuccessConcreteStep writeSuccessConcretePc
      (PcInList writeSuccessExitPcs) fromStep count before after ->
    ConfinedTrace writeSuccessConcreteStep writeSuccessConcretePc
      (PcInRanges writeSuccessExecutionPcRanges) fromStep count before after.
  Proof using All.
    intros Hinvariant Htrace.
    induction Htrace.
    - constructor.
    - destruct Hinvariant as
        (block & params & offset & entryState & Hinvariant & Hconsistent &
         Hoffset & ->).
      pose proof (phaseBBlockFamily block) as Hfamily.
      destruct (Hfamily executionArgs params entryState Hinvariant)
        as (_ & Hoffsets & _ & Hcovered & _).
      destruct (Hoffsets offset Hoffset)
        as (address & Hpc & Hblock & Hclassified).
      destruct Hclassified as [[Hregion HnotExit] | Hexit].
      + econstructor; try eassumption.
        apply IHHtrace.
        eapply blockInvariantPreserved.
        * intros currentArgs currentBlock currentParams currentOffset
            currentEntry index next Hcurrent HcurrentOffset Hstep.
          pose proof (phaseBBlockFamily currentBlock) as HcurrentFamily.
          destruct (HcurrentFamily currentArgs currentParams currentEntry
            Hcurrent) as (_ & _ & _ & HcurrentCovered & _).
          exact (HcurrentCovered currentOffset index next
            HcurrentOffset Hstep).
        * intros currentArgs currentBlock currentParams currentEntry Hcurrent.
          pose proof (phaseBBlockFamily currentBlock) as HcurrentFamily.
          destruct (HcurrentFamily currentArgs currentParams currentEntry
            Hcurrent) as (_ & _ & _ & _ & _ & _ & Hhandoff).
          exact Hhandoff.
        * exists block, params, offset, entryState.
          repeat split; try assumption.
        * exact H.
        * exact H0.
      + exfalso. eapply (H address Hpc). exact Hexit.
  Qed.

End PhaseBLedger.

Print Assumptions phaseBDecreasingExecutionObligations.
Print Assumptions phaseBPairedExecutionCertificate.
Print Assumptions phaseBExecutionCertificate.
Print Assumptions phaseBTerminalInvariant.
Print Assumptions phaseBInvariantTraceConfined.
