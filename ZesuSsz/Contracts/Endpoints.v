From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
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

Arguments DecodeBoundaryFailure {Decoded}.
Arguments DecodeBoundarySuccess {Decoded} _.

Definition InputIndexedBound (bound : nat -> nat) : Prop :=
  forall size : nat, size <= maxSszInputSize -> bound size < level1ContractFuel.

Definition ZkvmExitExecutionPc (pc : Z) : Prop :=
  PcInRanges zkvmExitExecutionPcRanges pc /\ pc <> zkvmExitTerminalPc.

(** An Islaris implementation can map each relational entry and exit to owned resources. *)
Record IslarisContractResources `{!islaG Sigma} `{!threadG}
    (Args Outcome : Type) : Type := {
  islarisCode : iProp Sigma;
  islarisEntry : Args -> iProp Sigma;
  islarisExit : Args -> Outcome -> iProp Sigma
}.

Definition IslarisContractSpec `{!Arch} `{!islaG Sigma} `{!threadG}
    {Args Outcome : Type} (entryPc exitPc : Z)
    (allows : Args -> Outcome -> Prop)
  (resources : IslarisContractResources Args Outcome) : iProp Sigma :=
  (islarisCode Args Outcome resources -∗
    ∀ args : Args,
      instr_body entryPc (
        islarisEntry Args Outcome resources args ∗
        instr_pre exitPc (
          ∃ outcome : Outcome,
            ⌜allows args outcome⌝ ∗
            islarisExit Args Outcome resources args outcome)))%I.

(** A contract model fixes its outcome relation and every owned resource. *)
Record IslarisContractModel (Args Outcome : Type) : Type := {
  islarisContractAllows : Args -> Outcome -> Prop;
  islarisContractStep : Z -> Z -> Prop;
  islarisContractResources : forall (Sigma : gFunctors)
    (HG : islaG Sigma) (HT : threadG),
    @IslarisContractResources Sigma HG HT Args Outcome
}.

Definition IslarisContractCorrect {Args Outcome : Type}
    (entryPc exitPc : Z) (model : IslarisContractModel Args Outcome) : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
    ⊢ @IslarisContractSpec riscv64_arch Sigma HG HT Args Outcome
      entryPc exitPc (islarisContractAllows Args Outcome model)
      (islarisContractResources Args Outcome model Sigma HG HT).

(** This model fixes the six native Level 1 resource contracts. *)
Record IslarisLevel1Model (Decoded : Type) : Type := {
  islarisReadInputContract : IslarisContractModel ReadInputArgs ReadInputOutcome;
  islarisAllocatorGetContract :
    IslarisContractModel AllocatorGetArgs AllocatorGetOutcome;
  islarisSszDecodeContract :
    IslarisContractModel DecodeBoundaryArgs (DecodeBoundaryOutcome Decoded);
  islarisWriteSuccessContract :
    IslarisContractModel (WriteSuccessArgs Decoded) ByteString;
  islarisWriteFailureContract :
    IslarisContractModel WriteFailureArgs ByteString;
  islarisZkvmExitContract : IslarisContractModel ZkvmExitArgs unit
}.

(** Phase 5 supplies termination separately. The writeSuccess field records
    only the Islaris state-correctness theorem during this phase. *)
Record IslarisLevel1ContractAssumptions
    {Decoded : Type} (model : IslarisLevel1Model Decoded) : Prop := {
  islarisLevel1ReadInput : exists bound : nat,
    Nat.lt bound level1ContractFuel /\
    NativeContractAssumption
      (IslarisContractCorrect ZesuSsz.Generated.Level1.readInputEntry
        0x14ccc
        (islarisReadInputContract Decoded model))
      (islarisContractStep _ _ (islarisReadInputContract Decoded model))
      (PcInRanges readInputExecutionPcRanges) (PcInList readInputExitPcs)
      ZesuSsz.Generated.Level1.readInputEntry bound;
  islarisLevel1AllocatorGet : exists bound : nat,
    Nat.lt bound level1ContractFuel /\
    NativeContractAssumption
      (IslarisContractCorrect ZesuSsz.Generated.Level1.allocatorGetEntry
        0x14cec (islarisAllocatorGetContract Decoded model))
      (islarisContractStep _ _ (islarisAllocatorGetContract Decoded model))
      (PcInRanges allocatorGetExecutionPcRanges) (PcInList allocatorGetExitPcs)
      ZesuSsz.Generated.Level1.allocatorGetEntry bound;
  islarisLevel1SszDecode : exists bound : nat,
    Nat.lt bound level1ContractFuel /\
    NativeContractAssumption
      (IslarisContractCorrect ZesuSsz.Generated.Level1.decodeInputEntry
        0x14cfc (islarisSszDecodeContract Decoded model))
      (islarisContractStep _ _ (islarisSszDecodeContract Decoded model))
      (PcInRanges decodeInputExecutionPcRanges) (PcInList decodeInputExitPcs)
      ZesuSsz.Generated.Level1.decodeInputEntry bound;
  islarisLevel1WriteSuccess :
    IslarisContractCorrect ZesuSsz.Generated.Level1.writeSuccessEntry
      0x14d10 (islarisWriteSuccessContract Decoded model);
  islarisLevel1WriteFailure : exists bound : nat,
    Nat.lt bound level1ContractFuel /\
    NativeContractAssumption
      (IslarisContractCorrect ZesuSsz.Generated.Level1.writeFailureEntry
        0x14d24 (islarisWriteFailureContract Decoded model))
      (islarisContractStep _ _ (islarisWriteFailureContract Decoded model))
      (PcInRanges writeFailureExecutionPcRanges) (PcInList writeFailureExitPcs)
      ZesuSsz.Generated.Level1.writeFailureEntry bound;
  islarisLevel1ZkvmExit : exists bound : nat,
    Nat.lt bound level1ContractFuel /\
    NativeContractAssumption
      (IslarisContractCorrect ZesuSsz.Generated.Level1.zkvmExitEntry
        zkvmExitTerminalPc (islarisZkvmExitContract Decoded model))
      (islarisContractStep _ _ (islarisZkvmExitContract Decoded model))
      ZkvmExitExecutionPc (PcInList zkvmExitExitPcs)
      ZesuSsz.Generated.Level1.zkvmExitEntry bound
}.
