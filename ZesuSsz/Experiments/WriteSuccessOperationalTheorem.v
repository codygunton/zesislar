From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import stdpp.base.
Require Import isla.opsem.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Contracts.ExecutionCertificate.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Experiments.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalDefinitions.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessPhaseBStateFrame
    (executionArgs : WriteSuccessExecutionArgs)
    (state : WriteSuccessConcreteState) : Prop :=
  let args := executionArgs.1 in
  let initial := executionArgs.2 in
  let regs := initial.1.1.(seq_regs) in
  let regs' := state.1.1.(seq_regs) in
  let sp := successStackPointer WriteSuccessObservation args in
  regs' !! "x2" = regs !! "x2" /\
  Forall (fun register => regs' !! register = regs !! register)
    ["x8"; "x9"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23";
     "x24"; "x25"; "x26"; "x27"] /\
  Forall (fun item =>
    match item.1 with
    | KindReg register => regs' !! register = regs !! register
    | KindField _ _ => True
    end) zesu_ram_sys_regs /\
  state.1.1.(seq_pc_reg) = "PC" /\
  state.1.1.(seq_nb_state) = false /\
  state.1.2.(seq_instrs) = initial.1.2.(seq_instrs) /\
  dom state.1.2.(seq_mem) = dom initial.1.2.(seq_mem) /\
  (forall address : bv 64,
    ~ (writeSuccessCalleeStackLow sp <= bv_unsigned address < sp) ->
    state.1.2.(seq_mem) !! address = initial.1.2.(seq_mem) !! address) /\
  (writeSuccessConcretePc state = Some 0x14d10 ->
    regs' !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14d10)) /\
    regs' !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x14d10))).

Definition writeSuccessPhaseBRecordProgress
    (executionArgs : WriteSuccessExecutionArgs)
    (state : WriteSuccessConcreteState) : Prop :=
  exists payloads pending,
    writeSuccessRecordedPayloads state.2 = Some payloads /\
    writeSuccessPublicBytes (concat payloads) ++ pending =
      writeSuccessEncodeObservation
        (successDecoded WriteSuccessObservation executionArgs.1) /\
    (writeSuccessConcretePc state = Some 0x14d10 -> pending = []).

Definition writeSuccessPhaseBConsistent
    (executionArgs : WriteSuccessExecutionArgs)
    (state : WriteSuccessConcreteState) : Prop :=
  writeSuccessPhaseBStateFrame executionArgs state /\
  writeSuccessPhaseBRecordProgress executionArgs state.

Definition PhaseBBlockFamily {Params : Type}
    (invariant : @Inv_ WriteSuccessConcreteState WriteSuccessExecutionArgs
      WriteSuccessBlock Params)
    (blockLength : WriteSuccessBlock -> nat)
    (blockSuccessor : WriteSuccessExecutionArgs -> WriteSuccessBlock ->
      Params -> WriteSuccessConcreteState -> WriteSuccessConcreteState)
    (rank : WriteSuccessExecutionArgs -> WriteSuccessConcreteState -> nat)
    (blockRecords : WriteSuccessExecutionArgs -> WriteSuccessBlock ->
      Params -> nat -> list WriteSuccessRecord)
    (block : WriteSuccessBlock) : Prop :=
  WriteSuccessBlockFamily invariant writeSuccessPhaseBConsistent
    blockLength blockSuccessor rank blockRecords block /\
  forall args params entryState,
    invariant args block params entryState ->
    forall offset,
      (offset <= blockLength block)%nat ->
      writeSuccessPhaseBConsistent args
        (iterate (blockSuccessor args block params) offset entryState).

Lemma writeSuccessPhaseBEntryConsistent args state :
  writeSuccessPairedEntry args state ->
  writeSuccessPhaseBConsistent args state.
Proof.
  intros (-> & Hentry).
  split.
  - unfold writeSuccessPhaseBStateFrame. cbn.
    unfold writeSuccessConcreteEntry in Hentry.
    destruct Hentry as (Hlog & Hpc & Hinitial & Hrepresentation & Hassumptions).
    unfold writeSuccessConcreteInitialState in Hinitial.
    destruct Hinitial as
      (Htrace & HpcReg & Hnb & Hcode & Htable & HpcLookup & Hx1 & Hx2 &
       Hx10 & Habi & Hsys & Hreturn & Halign & HstackLow & HstackHigh &
       Hstack & Hmmio).
    repeat split; try reflexivity; try assumption.
    + apply Forall_forall. intros register Hregister. reflexivity.
    + apply Forall_forall. intros item Hitem.
      destruct item as [kind shape]. destruct kind; reflexivity.
    + all: exfalso; rewrite Hpc in H; discriminate H.
    + exfalso. rewrite Hpc in H. discriminate H.
  - unfold writeSuccessPhaseBRecordProgress.
    exists [], (writeSuccessEncodeObservation
      (successDecoded WriteSuccessObservation args.1)).
    split.
    + cbn. apply writeSuccessConcreteEntryLogEmpty in Hentry. rewrite Hentry.
      reflexivity.
    + split; first reflexivity.
      intros Hexit. apply writeSuccessConcreteEntryPc in Hentry.
      rewrite Hentry in Hexit. discriminate Hexit.
Qed.

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
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessPrologue.
  Variable phaseBHeader :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessHeader.
  Variable phaseBTransactions :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessTransactions.
  Variable phaseBAccessLists :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessAccessLists.
  Variable phaseBStorageKeys :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessStorageKeys.
  Variable phaseBBlobHashes :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessBlobHashes.
  Variable phaseBAuthorizations :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessAuthorizations.
  Variable phaseBPostTransactions :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessPostTransactions.
  Variable phaseBWithdrawals :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessWithdrawals.
  Variable phaseBPostWithdrawals :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessPostWithdrawals.
  Variable phaseBSuffixHashes :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessSuffixHashes.
  Variable phaseBTail :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessTail.
  Variable phaseBEpilogue :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEpilogue.
  Variable phaseBWriteOutput :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessWriteOutput.
  Variable phaseBMemcpy :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessMemcpy.
  Variable phaseBEncoderInt :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderInt.
  Variable phaseBEncoderBoolean :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderBoolean.
  Variable phaseBEncoderOptionalU64 :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderOptionalU64.
  Variable phaseBEncoderBytes :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderBytes.
  Variable phaseBEncoderByteLists :
    PhaseBBlockFamily phaseBInvariant
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      WriteSuccessEncoderByteLists.

  Variable phaseBEntryBlock :
    forall args state,
      writeSuccessPairedEntry args state ->
      exists block params,
        phaseBInvariant args block params state.
  Variable phaseBEntryRankBound :
    forall args state,
      writeSuccessPairedEntry args state ->
      (phaseBRank args state <= writeSuccessInstructionBoundConstant)%nat.
  Variable phaseBRoundTrip : writeSuccessObservationRoundTrip.

  Lemma phaseBBlockFamily block :
    WriteSuccessBlockFamily phaseBInvariant writeSuccessPhaseBConsistent
      phaseBBlockLength phaseBBlockSuccessor phaseBRank phaseBBlockRecords
      block.
  Proof using All.
    destruct block;
      match goal with
      | H : PhaseBBlockFamily _ _ _ _ _ _ |- _ => exact (proj1 H)
      end.
  Qed.

  Lemma phaseBBlockLocalFacts block :
    forall args params entryState,
      phaseBInvariant args block params entryState ->
      forall offset,
        (offset <= phaseBBlockLength block)%nat ->
        writeSuccessPhaseBConsistent args
          (iterate (phaseBBlockSuccessor args block params) offset entryState).
  Proof using All.
    destruct block;
      match goal with
      | H : PhaseBBlockFamily _ _ _ _ _ _ |- _ => exact (proj2 H)
      end.
  Qed.

  Lemma phaseBEntryBlockWithLength args state :
    writeSuccessPairedEntry args state ->
    exists block params,
      phaseBInvariant args block params state /\
      writeSuccessPhaseBConsistent args state /\
      (0 < phaseBBlockLength block)%nat.
  Proof using All.
    intros Hentry.
    destruct (phaseBEntryBlock args state Hentry)
      as (block & params & Hinvariant).
    have Hconsistent := writeSuccessPhaseBEntryConsistent args state Hentry.
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
      (entryConsistent := writeSuccessPhaseBConsistent)
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
    blockExecutionInvariant phaseBInvariant writeSuccessPhaseBConsistent
      phaseBBlockLength phaseBBlockSuccessor (args, before) after.
  Proof using All.
    intros Hentry Htrace.
    destruct (phaseBEntryBlockWithLength (args, before) before
      (conj eq_refl Hentry))
      as (block & params & Hinvariant & Hconsistent & Hlength).
    pose proof (blockExecutionInvariantAtEntry phaseBInvariant
      writeSuccessPhaseBConsistent phaseBBlockLength phaseBBlockSuccessor
      (args, before) block params before Hinvariant Hconsistent Hlength)
      as HblockEntry.
    eapply (stoppedTraceInvariant writeSuccessConcreteStep
      writeSuccessConcretePc (PcInList writeSuccessExitPcs)
      (blockExecutionInvariant phaseBInvariant writeSuccessPhaseBConsistent
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
    blockExecutionInvariant phaseBInvariant writeSuccessPhaseBConsistent
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
          exact (conj Hinvariant
            (conj Hconsistent (conj Hoffset eq_refl))).
        * exact H.
        * exact H0.
      + exfalso. eapply (H address Hpc). exact Hexit.
  Qed.

  Lemma phaseBStoppedTraceConsistent args fromStep count before after :
    writeSuccessConcreteEntry args before ->
    StoppedTrace writeSuccessConcreteStep writeSuccessConcretePc
      (PcInList writeSuccessExitPcs) fromStep count before after ->
    writeSuccessPhaseBConsistent (args, before) after.
  Proof using All.
    intros Hentry Htrace.
    destruct (phaseBTerminalInvariant args fromStep count before after
      Hentry Htrace) as
      (block & params & offset & entryState & Hinvariant & Hconsistent &
       Hoffset & Hafter).
    subst after.
    apply (phaseBBlockLocalFacts block (args, before) params entryState
      Hinvariant offset). lia.
  Qed.

  Lemma phaseBConsistentAtExit executionArgs after :
    writeSuccessPhaseBConsistent executionArgs after ->
    writeSuccessConcretePc after = Some 0x14d10 ->
    writeSuccessObservedBytes after.2 =
      Some (writeSuccessEncodeObservation
        (successDecoded WriteSuccessObservation executionArgs.1)) /\
    writeSuccessPreservedState executionArgs.1 executionArgs.2 after.
  Proof using All.
    intros [Hframe Hrecords] Hpc.
    unfold writeSuccessPhaseBStateFrame in Hframe. cbn in Hframe.
    destruct Hframe as
      (Hx2 & Hsaved & Hsys & HpcReg & Hnb & Hinstrs & Hdom & Hmemory & Hreturn).
    specialize (Hreturn Hpc). destruct Hreturn as [HpcLookup Hx1].
    unfold writeSuccessPhaseBRecordProgress in Hrecords.
    destruct Hrecords as (payloads & pending & Hpayloads & Hencoded & Hcomplete).
    specialize (Hcomplete Hpc). subst pending. rewrite app_nil_r in Hencoded.
    split.
    - unfold writeSuccessObservedBytes. rewrite Hpayloads Hencoded. reflexivity.
    - unfold writeSuccessPreservedState. cbn. repeat split; assumption.
  Qed.

  Theorem writeSuccessLevel1Operational :
    ExecutionPathCertificate writeSuccessConcreteStep writeSuccessConcretePc
      writeSuccessConcreteEntry
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs) 0x14d30
      (fun _ => writeSuccessInstructionBoundConstant) /\
    (writeSuccessInstructionBoundConstant < level1ContractFuel)%nat /\
    forall args before fromStep count after,
      writeSuccessConcreteEntry args before ->
      StoppedTrace writeSuccessConcreteStep writeSuccessConcretePc
        (PcInList writeSuccessExitPcs) fromStep count before after ->
      writeSuccessConcretePc after = Some 0x14d10 ->
      writeSuccessObservedBytes after.2 =
        Some (writeSuccessEncodeObservation
          (successDecoded WriteSuccessObservation args)) /\
      writeSuccessDecodeObservation
        (writeSuccessEncodeObservation
          (successDecoded WriteSuccessObservation args)) =
        Some (successDecoded WriteSuccessObservation args) /\
      writeSuccessPreservedState args before after.
  Proof using All.
    split; first exact phaseBExecutionCertificate.
    split; first exact writeSuccessInstructionBoundBelowFuel.
    intros args before fromStep count after Hentry Htrace Hpc.
    destruct (phaseBConsistentAtExit (args, before) after
      (phaseBStoppedTraceConsistent args fromStep count before after Hentry Htrace)
      Hpc) as [Hobserved Hpreserved].
    split; first exact Hobserved. split; last exact Hpreserved.
    apply (writeSuccessDecodeFromRoundTrip phaseBRoundTrip).
    unfold writeSuccessConcreteEntry in Hentry.
    destruct Hentry as (_ & _ & _ & Hrepresentation & _).
    unfold writeSuccessConcreteRepresentation in Hrepresentation. tauto.
  Qed.

  Corollary writeSuccessOperationalImplements :
    Implements writeSuccessConcreteModel
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs)
      (writeSuccessContract writeSuccessConcreteModel
        (fun _ => writeSuccessInstructionBoundConstant)).
  Proof using All.
    intros args fromStep before Hentry.
    destruct phaseBExecutionCertificate as
      [HentryPc Hterminal Hprefixes Hprogress Hmaximal HnoInfinite].
    destruct (Hterminal args fromStep before Hentry)
      as (count & after & Hpositive & Hbound & Htrace &
          address & Hpc & Hexit).
    unfold PcInList in Hexit. cbn [writeSuccessExitPcs] in Hexit.
    destruct Hexit as [<- | []].
    assert (Hblock :
        blockExecutionInvariant phaseBInvariant writeSuccessPhaseBConsistent
          phaseBBlockLength phaseBBlockSuccessor (args, before) before).
    { destruct (phaseBEntryBlockWithLength (args, before) before
        (conj eq_refl Hentry))
        as (block & params & Hinvariant & Hconsistent & Hlength).
      eapply blockExecutionInvariantAtEntry; eassumption. }
    pose proof (phaseBInvariantTraceConfined (args, before) fromStep count
      before after Hblock Htrace) as Hconfined.
    destruct writeSuccessLevel1Operational as (_ & _ & Hcorrect).
    destruct (Hcorrect args before fromStep count after Hentry Htrace Hpc)
      as (Hobserved & Hdecoded & Hpreserved).
    exists count, after,
      (writeSuccessEncodeObservation
        (successDecoded WriteSuccessObservation args)).
    split; first exact Hpositive.
    split; first exact Hbound.
    split; first exact Hconfined.
    split.
    - exists 0x14d10. split; first exact Hpc.
      vm_compute. auto.
    - split; first exact Hdecoded. split; assumption.
  Qed.

  Corollary writeSuccessOperationalNativeExecutionContractAssumption :
    NativeExecutionContractAssumption
      (forall args before fromStep count after,
        writeSuccessConcreteEntry args before ->
        StoppedTrace writeSuccessConcreteStep writeSuccessConcretePc
          (PcInList writeSuccessExitPcs) fromStep count before after ->
        writeSuccessConcretePc after = Some 0x14d10 ->
        writeSuccessObservedBytes after.2 =
          Some (writeSuccessEncodeObservation
            (successDecoded WriteSuccessObservation args)) /\
        writeSuccessDecodeObservation
          (writeSuccessEncodeObservation
            (successDecoded WriteSuccessObservation args)) =
          Some (successDecoded WriteSuccessObservation args) /\
        writeSuccessPreservedState args before after)
      writeSuccessConcreteStep writeSuccessConcretePc
      writeSuccessConcreteEntry
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs) 0x14d30
      (fun _ => writeSuccessInstructionBoundConstant).
  Proof using All.
    apply nativeExecutionContractBridge.
    - intros args before fromStep count after Hentry Htrace Hpc.
      destruct writeSuccessLevel1Operational as (_ & _ & Hcorrect).
      exact (Hcorrect args before fromStep count after Hentry Htrace Hpc).
    - exact phaseBExecutionCertificate.
  Qed.

End PhaseBLedger.

Print Assumptions phaseBDecreasingExecutionObligations.
Print Assumptions phaseBPairedExecutionCertificate.
Print Assumptions phaseBExecutionCertificate.
Print Assumptions phaseBTerminalInvariant.
Print Assumptions phaseBInvariantTraceConfined.
Print Assumptions phaseBStoppedTraceConsistent.
Print Assumptions phaseBConsistentAtExit.
Print Assumptions writeSuccessLevel1Operational.
Print Assumptions writeSuccessOperationalImplements.
Print Assumptions writeSuccessOperationalNativeExecutionContractAssumption.
