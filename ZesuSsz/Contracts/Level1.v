From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.isla.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.

Import ListNotations.

Definition ByteString := list Z.
Definition maxSszInputSize : nat := 64 * 1024 * 1024.
Definition level1ContractFuel : nat := Nat.pow 2 160.

Record ReadInputArgs : Type := {
  readReturnAddress : Z;
  readBufferSlot : Z;
  readSizeSlot : Z;
  readSavedFrameAddress : Z;
  readSavedReturnAddress : Z;
  readInputBytes : ByteString
}.

Record ReadInputOutcome : Type := { readInputAddress : Z }.

Record AllocatorGetArgs : Type := {
  allocatorReturnAddress : Z;
  allocatorStackPointer : Z;
  allocatorInputAddress : Z;
  allocatorInput : ByteString;
  allocatorSavedReturnAddress : Z
}.

Record AllocatorGetOutcome : Type := {
  allocatorStateAddress : Z;
  allocatorVtableAddress : Z
}.

Record DecodeBoundaryArgs : Type := {
  decodeReturnAddress : Z;
  decodeSavedReturnAddress : Z;
  decodeInputAddress : Z;
  decodeInput : ByteString;
  decodeStackPointer : Z;
  decodeAllocatorStateAddress : Z;
  decodeAllocatorVtableAddress : Z
}.

Inductive DecodeBoundaryOutcome (Decoded : Type) : Type :=
| DecodeBoundaryFailure
| DecodeBoundarySuccess (decoded : Decoded).

Record WriteSuccessArgs (Decoded : Type) : Type := {
  successReturnAddress : Z;
  successStackPointer : Z;
  successDecodedAddress : Z;
  successDecoded : Decoded;
  successInputSize : nat
}.

Record WriteFailureArgs : Type := { failureReturnAddress : Z }.
Record ZkvmExitArgs : Type := { zkvmExitCode : Z }.

(** The adapter supplies the concrete Islaris state predicates. The contracts below
    preserve the argument, outcome, control-flow, and semantic structure of Level 1. *)
Record Level1MachineModel (State Decoded : Type) : Type := {
  endpointStep : nat -> State -> State -> Prop;
  endpointPc : State -> option Z;

  readInputEntry : ReadInputArgs -> State -> Prop;
  readInputExit : ReadInputArgs -> ReadInputOutcome -> State -> State -> Prop;

  allocatorGetEntry : AllocatorGetArgs -> State -> Prop;
  allocatorGetExit : AllocatorGetArgs -> AllocatorGetOutcome -> State -> State -> Prop;

  decodeBoundaryEntry : DecodeBoundaryArgs -> State -> Prop;
  decodeBoundaryExit : DecodeBoundaryArgs -> DecodeBoundaryOutcome Decoded -> State -> State -> Prop;

  writeSuccessEntry : WriteSuccessArgs Decoded -> State -> Prop;
  writeSuccessExit : WriteSuccessArgs Decoded -> ByteString -> State -> State -> Prop;

  writeFailureEntry : WriteFailureArgs -> State -> Prop;
  writeFailureExit : WriteFailureArgs -> ByteString -> State -> State -> Prop;

  zkvmExitEntry : ZkvmExitArgs -> State -> Prop;
  zkvmExitPost : ZkvmExitArgs -> unit -> State -> State -> Prop;

  referenceDecodes : ByteString -> Decoded -> Prop;
  decodedResultRelModuloKnownBugs : ByteString -> Decoded -> Decoded -> Prop;
  avoidsReviewedDomainDivergences : ByteString -> Decoded -> Prop;
  knownBugApplies : KnownBug -> ByteString -> Decoded -> Prop;
  decodeObservationSuccess : ByteString -> Decoded -> Prop;
  decodeObservationFailure : ByteString -> Prop
}.

Arguments DecodeBoundaryFailure {Decoded}.
Arguments DecodeBoundarySuccess {Decoded} _.

Definition StrictDecodeMeaning {State Decoded}
    (model : Level1MachineModel State Decoded)
    (args : DecodeBoundaryArgs) (outcome : DecodeBoundaryOutcome Decoded) : Prop :=
  match outcome with
  | DecodeBoundaryFailure =>
      ~ exists decoded, referenceDecodes State Decoded model (decodeInput args) decoded
  | DecodeBoundarySuccess zesu =>
      exists sail,
        referenceDecodes State Decoded model (decodeInput args) sail /\
        decodedResultRelModuloKnownBugs State Decoded model (decodeInput args) zesu sail
  end.

Definition DecodeMeaningModuloKnownBugs {State Decoded}
    (model : Level1MachineModel State Decoded)
    (args : DecodeBoundaryArgs) (outcome : DecodeBoundaryOutcome Decoded) : Prop :=
  match outcome with
  | DecodeBoundaryFailure =>
      ~ exists decoded, referenceDecodes State Decoded model (decodeInput args) decoded
  | DecodeBoundarySuccess zesu =>
      (exists sail,
        referenceDecodes State Decoded model (decodeInput args) sail /\
        decodedResultRelModuloKnownBugs State Decoded model (decodeInput args) zesu sail /\
        avoidsReviewedDomainDivergences State Decoded model (decodeInput args) zesu) \/
      ((~ exists sail, referenceDecodes State Decoded model (decodeInput args) sail) /\
       exists bug, In bug knownBugs /\
         knownBugApplies State Decoded model bug (decodeInput args) zesu)
  end.

Definition readInputContract {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : ReadInputArgs -> nat) :=
  {| contractAllows := fun _ _ => True;
     contractEntry := readInputEntry State Decoded model;
     contractExit := readInputExit State Decoded model;
     contractStepBound := bound |}.

Definition allocatorGetContract {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : AllocatorGetArgs -> nat) :=
  {| contractAllows := fun _ _ => True;
     contractEntry := allocatorGetEntry State Decoded model;
     contractExit := allocatorGetExit State Decoded model;
     contractStepBound := bound |}.

Definition decodeContractModuloKnownBugs {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : DecodeBoundaryArgs -> nat) :=
  {| contractAllows := DecodeMeaningModuloKnownBugs model;
     contractEntry := decodeBoundaryEntry State Decoded model;
     contractExit := decodeBoundaryExit State Decoded model;
     contractStepBound := bound |}.

Definition writeSuccessContract {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : WriteSuccessArgs Decoded -> nat) :=
  {| contractAllows := fun args bytes =>
       decodeObservationSuccess State Decoded model bytes (successDecoded Decoded args);
     contractEntry := writeSuccessEntry State Decoded model;
     contractExit := writeSuccessExit State Decoded model;
     contractStepBound := bound |}.

Definition writeFailureContract {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : WriteFailureArgs -> nat) :=
  {| contractAllows := fun _ bytes => decodeObservationFailure State Decoded model bytes;
     contractEntry := writeFailureEntry State Decoded model;
     contractExit := writeFailureExit State Decoded model;
     contractStepBound := bound |}.

Definition zkvmExitContract {State Decoded}
    (model : Level1MachineModel State Decoded) (bound : ZkvmExitArgs -> nat) :=
  {| contractAllows := fun _ _ => True;
     contractEntry := zkvmExitEntry State Decoded model;
     contractExit := zkvmExitPost State Decoded model;
     contractStepBound := bound |}.

Definition Implements {State Decoded Args Outcome}
    (model : Level1MachineModel State Decoded)
    (region exitPc : Z -> Prop)
    (contract : RelationalMachineContract State Args Outcome) : Prop :=
  ContractImplements (endpointStep State Decoded model)
    (endpointPc State Decoded model) region exitPc contract.

Definition InputIndexedBound (bound : nat -> nat) : Prop :=
  forall size : nat, size <= maxSszInputSize -> bound size < level1ContractFuel.

Definition ZkvmExitExecutionPc (pc : Z) : Prop :=
  PcInRanges zkvmExitExecutionPcRanges pc /\ pc <> zkvmExitTerminalPc.

Record Level1ContractAssumptions {State Decoded}
    (model : Level1MachineModel State Decoded) : Prop := {
  level1ReadInput : exists bound, InputIndexedBound bound /\
    Implements model (PcInRanges readInputExecutionPcRanges) (PcInList readInputExitPcs)
      (readInputContract model (fun args => bound (length (readInputBytes args))));
  level1AllocatorGet : exists bound, InputIndexedBound bound /\
    Implements model (PcInRanges allocatorGetExecutionPcRanges) (PcInList allocatorGetExitPcs)
      (allocatorGetContract model (fun args => bound (length (allocatorInput args))));
  level1SszDecode : exists bound, InputIndexedBound bound /\
    Implements model (PcInRanges decodeInputExecutionPcRanges) (PcInList decodeInputExitPcs)
      (decodeContractModuloKnownBugs model (fun args => bound (length (decodeInput args))));
  level1WriteSuccess : exists bound, InputIndexedBound bound /\
    Implements model (PcInRanges writeSuccessExecutionPcRanges) (PcInList writeSuccessExitPcs)
      (writeSuccessContract model (fun args => bound (successInputSize Decoded args)));
  level1WriteFailure : exists bound : nat, Nat.lt bound level1ContractFuel /\
    Implements model (PcInRanges writeFailureExecutionPcRanges) (PcInList writeFailureExitPcs)
      (writeFailureContract model (fun _ => bound));
  level1ZkvmExit : exists bound : nat, Nat.lt bound level1ContractFuel /\
    Implements model ZkvmExitExecutionPc (PcInList zkvmExitExitPcs)
      (zkvmExitContract model (fun _ => bound))
}.

(** An Islaris implementation can map each relational entry and exit to owned resources. *)
Record IslarisContractResources `{!islaG Sigma} `{!threadG}
    (Args Outcome : Type) : Type := {
  islarisEntry : Args -> iProp Sigma;
  islarisExit : Args -> Outcome -> iProp Sigma
}.

Definition IslarisContractSpec `{!Arch} `{!islaG Sigma} `{!threadG}
    {Args Outcome : Type} (entryPc : Z)
  (resources : IslarisContractResources Args Outcome) : iProp Sigma :=
  (∀ args : Args, islarisEntry Args Outcome resources args -∗
    instr_body entryPc
      (∃ outcome : Outcome, islarisExit Args Outcome resources args outcome))%I.
