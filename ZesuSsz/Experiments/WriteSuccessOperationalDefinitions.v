From Coq Require Import Lia Lists.List ZArith.ZArith Arith.PeanoNat.
Require Import stdpp.base.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Contracts.ExecutionCertificate.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessBlockFramework.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessInstructionBoundConstant : nat :=
  (Nat.pow (S (Nat.pow 2 29)) 4 * Nat.pow 2 20)%nat.

Lemma writeSuccessPowerTwoAtLeastOne exponent :
  1 <= Nat.pow 2 exponent.
Proof. induction exponent; simpl; lia. Qed.

Lemma writeSuccessInstructionBoundBelowFuel :
  (writeSuccessInstructionBoundConstant < level1ContractFuel)%nat.
Proof.
  unfold writeSuccessInstructionBoundConstant, level1ContractFuel.
  assert (Hbase : (S (Nat.pow 2 29) <= Nat.pow 2 30)%nat).
  { rewrite (Nat.pow_succ_r 2 29 (Nat.le_0_l 29)).
    pose proof (writeSuccessPowerTwoAtLeastOne 29). lia. }
  assert (Hfour :
      (Nat.pow (S (Nat.pow 2 29)) 4 <=
       Nat.pow (Nat.pow 2 30) 4)%nat).
  { apply Nat.pow_le_mono_l. exact Hbase. }
  assert (Hscale :
      (Nat.pow (S (Nat.pow 2 29)) 4 * Nat.pow 2 20 <=
       Nat.pow (Nat.pow 2 30) 4 * Nat.pow 2 20)%nat).
  { exact (Nat.mul_le_mono_r _ _ _ Hfour). }
  refine (Nat.le_lt_trans _ _ _ Hscale _).
  rewrite <- Nat.pow_mul_r.
  rewrite <- Nat.pow_add_r.
  apply Nat.pow_lt_mono_r; lia.
Qed.

Definition writeSuccessEntryRepresentation
    (decoded : WriteSuccessObservation) (state : WriteSuccessConcreteState) : Prop :=
  exists address,
    writeSuccessConcreteRepresentation decoded state.1.2.(seq_mem) address.

Lemma writeSuccessEntryRepresentationLaw args state :
  writeSuccessConcreteEntry args state ->
  writeSuccessEntryRepresentation
    (successDecoded WriteSuccessObservation args) state.
Proof.
  intros (_ & _ & _ & Hrepresentation & _).
  exists (successDecodedAddress WriteSuccessObservation args).
  exact Hrepresentation.
Qed.

Definition writeSuccessConcreteModel :
    Level1MachineModel WriteSuccessConcreteState WriteSuccessObservation.
Proof.
  refine {|
    ZesuSsz.Contracts.Level1.endpointStep := writeSuccessConcreteStep;
    ZesuSsz.Contracts.Level1.endpointPc := writeSuccessConcretePc;
    ZesuSsz.Contracts.Level1.readInputEntry := fun _ _ => False;
    ZesuSsz.Contracts.Level1.readInputExit := fun _ _ _ _ => False;
    ZesuSsz.Contracts.Level1.allocatorGetEntry := fun _ _ => False;
    ZesuSsz.Contracts.Level1.allocatorGetExit := fun _ _ _ _ => False;
    ZesuSsz.Contracts.Level1.decodeBoundaryEntry := fun _ _ => False;
    ZesuSsz.Contracts.Level1.decodeBoundaryExit := fun _ _ _ _ => False;
    ZesuSsz.Contracts.Level1.writeSuccessEntry := writeSuccessConcreteEntry;
    ZesuSsz.Contracts.Level1.writeSuccessEntryRepresentation :=
      writeSuccessEntryRepresentation;
    ZesuSsz.Contracts.Level1.writeSuccessEntryRepresents :=
      writeSuccessEntryRepresentationLaw;
    ZesuSsz.Contracts.Level1.writeSuccessExit := fun _ bytes _ after =>
      writeSuccessConcretePc after = Some 0x14d10 /\
      writeSuccessObservedBytes after.2 = Some bytes;
    ZesuSsz.Contracts.Level1.writeFailureEntry := fun _ _ => False;
    ZesuSsz.Contracts.Level1.writeFailureExit := fun _ _ _ _ => False;
    ZesuSsz.Contracts.Level1.zkvmExitEntry := fun _ _ => False;
    ZesuSsz.Contracts.Level1.zkvmExitPost := fun _ _ _ _ => False;
    ZesuSsz.Contracts.Level1.referenceDecodes := fun bytes decoded =>
      writeSuccessDecodeObservation bytes = Some decoded;
    ZesuSsz.Contracts.Level1.decodedResultRelModuloKnownBugs :=
      fun bytes _ decoded =>
      writeSuccessDecodeObservation bytes = Some decoded;
    ZesuSsz.Contracts.Level1.avoidsReviewedDomainDivergences :=
      fun _ _ => True;
    ZesuSsz.Contracts.Level1.knownBugApplies := fun _ _ _ => False;
    ZesuSsz.Contracts.Level1.decodeObservationSuccess := fun bytes decoded =>
      writeSuccessDecodeObservation bytes = Some decoded;
    ZesuSsz.Contracts.Level1.decodeObservationFailure := fun bytes =>
      writeSuccessDecodeObservation bytes = None
  |}.
Defined.

Definition writeSuccessProloguePc (address : Z) : Prop :=
  (0x14d30 <= address < 0x14d80)%Z.
Definition writeSuccessHeaderPc (address : Z) : Prop :=
  (0x14d80 <= address < 0x14f00)%Z.
Definition writeSuccessTransactionsPc (address : Z) : Prop :=
  (0x14f00 <= address < 0x151d4 \/
   0x153b4 <= address < 0x153d0 \/
   0x15564 <= address < 0x15584 \/
   0x15620 <= address < 0x15668)%Z.
Definition writeSuccessAccessListsPc (address : Z) : Prop :=
  (0x151d4 <= address < 0x1521c \/
   0x153b4 <= address < 0x153c0)%Z.
Definition writeSuccessStorageKeysPc (address : Z) : Prop :=
  (0x1521c <= address < 0x153b4)%Z.
Definition writeSuccessBlobHashesPc (address : Z) : Prop :=
  (0x153d0 <= address < 0x15564)%Z.
Definition writeSuccessAuthorizationsPc (address : Z) : Prop :=
  (0x15584 <= address < 0x15620)%Z.
Definition writeSuccessPostTransactionsPc (address : Z) : Prop :=
  (0x15668 <= address < 0x15694)%Z.
Definition writeSuccessWithdrawalsPc (address : Z) : Prop :=
  (0x15694 <= address < 0x156e8)%Z.
Definition writeSuccessPostWithdrawalsPc (address : Z) : Prop :=
  (0x156e8 <= address < 0x15754)%Z.
Definition writeSuccessSuffixHashesPc (address : Z) : Prop :=
  (0x15754 <= address < 0x158e0)%Z.
Definition writeSuccessTailPc (address : Z) : Prop :=
  (0x158e0 <= address < 0x159d8)%Z.
Definition writeSuccessEpiloguePc (address : Z) : Prop :=
  address = 0x14d10 \/ (0x159d8 <= address < 0x15a14)%Z.
Definition writeSuccessWriteOutputPc (address : Z) : Prop :=
  (0x10190 <= address < 0x101c4)%Z.
Definition writeSuccessMemcpyPc (address : Z) : Prop :=
  (0x101d4 <= address < 0x101f8)%Z.
Definition writeSuccessEncoderIntPc (address : Z) : Prop :=
  (0x15cb0 <= address < 0x15d38)%Z.
Definition writeSuccessEncoderBooleanPc (address : Z) : Prop :=
  (0x15b9c <= address < 0x15bc8)%Z.
Definition writeSuccessEncoderOptionalU64Pc (address : Z) : Prop :=
  (0x15bc8 <= address < 0x15c10)%Z.
Definition writeSuccessEncoderBytesPc (address : Z) : Prop :=
  (0x15c6c <= address < 0x15cb0)%Z.
Definition writeSuccessEncoderByteListsPc (address : Z) : Prop :=
  (0x15c10 <= address < 0x15c6c)%Z.

Definition writeSuccessBlockFamilies : list (Z -> Prop) := [
  writeSuccessProloguePc; writeSuccessHeaderPc;
  writeSuccessTransactionsPc; writeSuccessAccessListsPc;
  writeSuccessStorageKeysPc; writeSuccessBlobHashesPc;
  writeSuccessAuthorizationsPc; writeSuccessPostTransactionsPc;
  writeSuccessWithdrawalsPc; writeSuccessPostWithdrawalsPc;
  writeSuccessSuffixHashesPc; writeSuccessTailPc; writeSuccessEpiloguePc;
  writeSuccessWriteOutputPc; writeSuccessMemcpyPc; writeSuccessEncoderIntPc;
  writeSuccessEncoderBooleanPc; writeSuccessEncoderOptionalU64Pc;
  writeSuccessEncoderBytesPc; writeSuccessEncoderByteListsPc
].

Lemma writeSuccessPcInBlockFamilies address :
  PcInRanges writeSuccessExecutionPcRanges address ->
  exists family,
    In family writeSuccessBlockFamilies /\ family address.
Proof.
  intros (lower & upper & Hin & Hrange).
  cbn in Hin.
  destruct Hin as [Hin|[Hin|[Hin|[Hin|[]]]]]; inversion Hin; subst;
    clear Hin.
  - exists writeSuccessWriteOutputPc. split; [cbn; tauto|].
    unfold writeSuccessWriteOutputPc. lia.
  - exists writeSuccessMemcpyPc. split; [cbn; tauto|].
    unfold writeSuccessMemcpyPc. lia.
  - destruct (Z_lt_ge_dec address 0x14d80).
    + exists writeSuccessProloguePc. split; [cbn; tauto|].
      unfold writeSuccessProloguePc. lia.
    + destruct (Z_lt_ge_dec address 0x14f00).
      * exists writeSuccessHeaderPc. split; [cbn; tauto|].
        unfold writeSuccessHeaderPc. lia.
      * destruct (Z_lt_ge_dec address 0x151d4).
        -- exists writeSuccessTransactionsPc. split; [cbn; tauto|].
           unfold writeSuccessTransactionsPc. lia.
        -- destruct (Z_lt_ge_dec address 0x1521c).
           ++ exists writeSuccessAccessListsPc. split; [cbn; tauto|].
              unfold writeSuccessAccessListsPc. lia.
           ++ destruct (Z_lt_ge_dec address 0x153b4).
              ** exists writeSuccessStorageKeysPc. split; [cbn; tauto|].
                 unfold writeSuccessStorageKeysPc. lia.
              ** destruct (Z_lt_ge_dec address 0x153d0).
                 --- exists writeSuccessTransactionsPc. split; [cbn; tauto|].
                     unfold writeSuccessTransactionsPc. lia.
                 --- destruct (Z_lt_ge_dec address 0x15564).
                     +++ exists writeSuccessBlobHashesPc. split; [cbn; tauto|].
                         unfold writeSuccessBlobHashesPc. lia.
                     +++ destruct (Z_lt_ge_dec address 0x15584).
                         *** exists writeSuccessTransactionsPc. split; [cbn; tauto|].
                             unfold writeSuccessTransactionsPc. lia.
                         *** destruct (Z_lt_ge_dec address 0x15620).
                             ---- exists writeSuccessAuthorizationsPc. split; [cbn; tauto|].
                                  unfold writeSuccessAuthorizationsPc. lia.
                             ---- destruct (Z_lt_ge_dec address 0x15668).
                                  ++++ exists writeSuccessTransactionsPc. split; [cbn; tauto|].
                                       unfold writeSuccessTransactionsPc. lia.
                                  ++++ destruct (Z_lt_ge_dec address 0x15694).
                                       **** exists writeSuccessPostTransactionsPc. split; [cbn; tauto|].
                                            unfold writeSuccessPostTransactionsPc. lia.
                                       **** destruct (Z_lt_ge_dec address 0x156e8).
                                            +++++ exists writeSuccessWithdrawalsPc. split; [cbn; tauto|].
                                                  unfold writeSuccessWithdrawalsPc. lia.
                                            +++++ destruct (Z_lt_ge_dec address 0x15754).
                                                  { exists writeSuccessPostWithdrawalsPc. split; [cbn; tauto|].
                                                    unfold writeSuccessPostWithdrawalsPc. lia. }
                                                  destruct (Z_lt_ge_dec address 0x158e0).
                                                  { exists writeSuccessSuffixHashesPc. split; [cbn; tauto|].
                                                    unfold writeSuccessSuffixHashesPc. lia. }
                                                  destruct (Z_lt_ge_dec address 0x159d8).
                                                  { exists writeSuccessTailPc. split; [cbn; tauto|].
                                                    unfold writeSuccessTailPc. lia. }
                                                  exists writeSuccessEpiloguePc. split; [cbn; tauto|].
                                                  unfold writeSuccessEpiloguePc. lia.
  - destruct (Z_lt_ge_dec address 0x15bc8).
    + exists writeSuccessEncoderBooleanPc. split; [cbn; tauto|].
      unfold writeSuccessEncoderBooleanPc. lia.
    + destruct (Z_lt_ge_dec address 0x15c10).
      * exists writeSuccessEncoderOptionalU64Pc. split; [cbn; tauto|].
        unfold writeSuccessEncoderOptionalU64Pc. lia.
      * destruct (Z_lt_ge_dec address 0x15c6c).
        -- exists writeSuccessEncoderByteListsPc. split; [cbn; tauto|].
           unfold writeSuccessEncoderByteListsPc. lia.
        -- destruct (Z_lt_ge_dec address 0x15cb0).
           ++ exists writeSuccessEncoderBytesPc. split; [cbn; tauto|].
              unfold writeSuccessEncoderBytesPc. lia.
           ++ exists writeSuccessEncoderIntPc. split; [cbn; tauto|].
              unfold writeSuccessEncoderIntPc. lia.
Qed.

Inductive WriteSuccessBlock : Type :=
| WriteSuccessPrologue
| WriteSuccessHeader
| WriteSuccessTransactions
| WriteSuccessAccessLists
| WriteSuccessStorageKeys
| WriteSuccessBlobHashes
| WriteSuccessAuthorizations
| WriteSuccessPostTransactions
| WriteSuccessWithdrawals
| WriteSuccessPostWithdrawals
| WriteSuccessSuffixHashes
| WriteSuccessTail
| WriteSuccessEpilogue
| WriteSuccessWriteOutput
| WriteSuccessMemcpy
| WriteSuccessEncoderInt
| WriteSuccessEncoderBoolean
| WriteSuccessEncoderOptionalU64
| WriteSuccessEncoderBytes
| WriteSuccessEncoderByteLists.

Definition writeSuccessBlockPc (block : WriteSuccessBlock) : Z -> Prop :=
  match block with
  | WriteSuccessPrologue => writeSuccessProloguePc
  | WriteSuccessHeader => writeSuccessHeaderPc
  | WriteSuccessTransactions => writeSuccessTransactionsPc
  | WriteSuccessAccessLists => writeSuccessAccessListsPc
  | WriteSuccessStorageKeys => writeSuccessStorageKeysPc
  | WriteSuccessBlobHashes => writeSuccessBlobHashesPc
  | WriteSuccessAuthorizations => writeSuccessAuthorizationsPc
  | WriteSuccessPostTransactions => writeSuccessPostTransactionsPc
  | WriteSuccessWithdrawals => writeSuccessWithdrawalsPc
  | WriteSuccessPostWithdrawals => writeSuccessPostWithdrawalsPc
  | WriteSuccessSuffixHashes => writeSuccessSuffixHashesPc
  | WriteSuccessTail => writeSuccessTailPc
  | WriteSuccessEpilogue => writeSuccessEpiloguePc
  | WriteSuccessWriteOutput => writeSuccessWriteOutputPc
  | WriteSuccessMemcpy => writeSuccessMemcpyPc
  | WriteSuccessEncoderInt => writeSuccessEncoderIntPc
  | WriteSuccessEncoderBoolean => writeSuccessEncoderBooleanPc
  | WriteSuccessEncoderOptionalU64 => writeSuccessEncoderOptionalU64Pc
  | WriteSuccessEncoderBytes => writeSuccessEncoderBytesPc
  | WriteSuccessEncoderByteLists => writeSuccessEncoderByteListsPc
  end.

Definition WriteSuccessExecutionArgs : Type :=
  (WriteSuccessArgs WriteSuccessObservation * WriteSuccessConcreteState)%type.

Definition writeSuccessPairedEntry
    (executionArgs : WriteSuccessExecutionArgs)
    (state : WriteSuccessConcreteState) : Prop :=
  state = executionArgs.2 /\
  writeSuccessConcreteEntry executionArgs.1 executionArgs.2.

Definition WriteSuccessBlockFamily
    {Params : Type}
    (invariant : Inv_ (State := WriteSuccessConcreteState)
      (Args := WriteSuccessExecutionArgs)
      (Block := WriteSuccessBlock) (Params := Params))
    (entryConsistent : WriteSuccessExecutionArgs ->
      WriteSuccessConcreteState -> Prop)
    (blockLength : WriteSuccessBlock -> nat)
    (blockSuccessor : WriteSuccessExecutionArgs -> WriteSuccessBlock ->
      Params -> WriteSuccessConcreteState -> WriteSuccessConcreteState)
    (rank : WriteSuccessExecutionArgs ->
      WriteSuccessConcreteState -> nat)
    (blockRecords : WriteSuccessExecutionArgs -> WriteSuccessBlock ->
      Params -> nat -> list WriteSuccessRecord)
    (block : WriteSuccessBlock) : Prop :=
  forall args params entryState,
    invariant args block params entryState ->
    (0 < blockLength block)%nat /\
    (forall offset : nat,
      (offset < blockLength block)%nat ->
      exists address,
        writeSuccessConcretePc
          (iterate (blockSuccessor args block params) offset entryState) =
          Some address /\
        writeSuccessBlockPc block address /\
        ((PcInRanges writeSuccessExecutionPcRanges address /\
          ~ PcInList writeSuccessExitPcs address) \/
         PcInList writeSuccessExitPcs address)) /\
    (forall (offset index : nat),
      (offset < blockLength block)%nat ->
      (forall address,
        writeSuccessConcretePc
          (iterate (blockSuccessor args block params) offset entryState) =
          Some address -> ~ PcInList writeSuccessExitPcs address) ->
      writeSuccessConcreteStep index
        (iterate (blockSuccessor args block params) offset entryState)
        (iterate (blockSuccessor args block params) (S offset) entryState)) /\
    (forall (offset index : nat) after,
      (offset < blockLength block)%nat ->
      writeSuccessConcreteStep index
        (iterate (blockSuccessor args block params) offset entryState) after ->
      after = iterate (blockSuccessor args block params) (S offset) entryState) /\
    (forall offset : nat,
      (offset < blockLength block)%nat ->
      (forall address,
        writeSuccessConcretePc
          (iterate (blockSuccessor args block params) offset entryState) =
          Some address -> ~ PcInList writeSuccessExitPcs address) ->
      (rank args
          (iterate (blockSuccessor args block params) (S offset) entryState) <
       rank args
          (iterate (blockSuccessor args block params) offset entryState))%nat) /\
    (forall offset : nat,
      (offset <= blockLength block)%nat ->
      (iterate (blockSuccessor args block params) offset entryState).2 =
        entryState.2 ++ blockRecords args block params offset) /\
    (exists nextBlock nextParams,
      invariant args nextBlock nextParams
        (iterate (blockSuccessor args block params)
          (blockLength block) entryState) /\
      entryConsistent args
        (iterate (blockSuccessor args block params)
          (blockLength block) entryState) /\
      (0 < blockLength nextBlock)%nat).

Print Assumptions writeSuccessInstructionBoundBelowFuel.
Print Assumptions writeSuccessEntryRepresentationLaw.
Print Assumptions writeSuccessPcInBlockFamilies.
