From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_00 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderValueTransactions.
Require Import ZesuSsz.Experiments.WriteSuccessLoadHeader.
Require Import ZesuSsz.Experiments.WriteSuccessNativeCode.
Require Import ZesuSsz.Experiments.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Experiments.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.

Import ListNotations.

(** This witness records the concrete data that the native proof must relate to
    the abstract [WriteSuccessArgs] value.  The existing block proofs expose
    these fields, but they do not yet establish this relation. *)
Record writeSuccessNativeWitness (Decoded : Type) : Type := {
  writeSuccessEntrySp : bv 64;
  writeSuccessDecodedPointer : bv 64;
  writeSuccessReturnValue : bv 64;
  writeSuccessSavedS0 : bv 64;
  writeSuccessSavedS1 : bv 64;
  writeSuccessSavedS2 : bv 64;
  writeSuccessSavedS3 : bv 64;
  writeSuccessSavedS4 : bv 64;
  writeSuccessSavedS5 : bv 64;
  writeSuccessSavedS6 : bv 64;
  writeSuccessSavedS7 : bv 64;
  writeSuccessSavedS8 : bv 64;
  writeSuccessSavedS9 : bv 64;
  writeSuccessSavedS10 : bv 64;
  writeSuccessSavedS11 : bv 64;
  writeSuccessDecodedBytes : list (bv 8);
  writeSuccessSourceBytes : list (bv 8);
  writeSuccessValues : list (bv 64);
  writeSuccessPayload : list (bv 8);
  writeSuccessTraceTail : spec;
  writeSuccessTransactionBase : Z;
  writeSuccessTransactions : list writeSuccessTransaction;
  writeSuccessTransactionBytes : list (bv 8)
}.

Arguments writeSuccessEntrySp {Decoded} _.
Arguments writeSuccessDecodedPointer {Decoded} _.
Arguments writeSuccessReturnValue {Decoded} _.
Arguments writeSuccessSavedS0 {Decoded} _.
Arguments writeSuccessSavedS1 {Decoded} _.
Arguments writeSuccessSavedS2 {Decoded} _.
Arguments writeSuccessSavedS3 {Decoded} _.
Arguments writeSuccessSavedS4 {Decoded} _.
Arguments writeSuccessSavedS5 {Decoded} _.
Arguments writeSuccessSavedS6 {Decoded} _.
Arguments writeSuccessSavedS7 {Decoded} _.
Arguments writeSuccessSavedS8 {Decoded} _.
Arguments writeSuccessSavedS9 {Decoded} _.
Arguments writeSuccessSavedS10 {Decoded} _.
Arguments writeSuccessSavedS11 {Decoded} _.
Arguments writeSuccessDecodedBytes {Decoded} _.
Arguments writeSuccessSourceBytes {Decoded} _.
Arguments writeSuccessValues {Decoded} _.
Arguments writeSuccessPayload {Decoded} _.
Arguments writeSuccessTraceTail {Decoded} _.
Arguments writeSuccessTransactionBase {Decoded} _.
Arguments writeSuccessTransactions {Decoded} _.
Arguments writeSuccessTransactionBytes {Decoded} _.

Definition writeSuccessFrameSp {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : bv 64 :=
  (writeSuccessEntrySp witness - BV 64 2000)%bv.

Definition writeSuccessWitnessWellFormed {Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    : Prop :=
  successStackPointer Decoded args = bv_unsigned (writeSuccessEntrySp witness) /\
  successDecodedAddress Decoded args = bv_unsigned (writeSuccessDecodedPointer witness) /\
  successReturnAddress Decoded args = 0x14d10 /\
  writeSuccessReturnValue witness =
    Z_to_bv 64 (successReturnAddress Decoded args) /\
  bv_unsigned (writeSuccessDecodedPointer witness) =
    (bv_unsigned (writeSuccessEntrySp witness) + 32)%Z /\
  length (writeSuccessDecodedBytes witness) = 848%nat /\
  length (writeSuccessSourceBytes witness) = 720%nat /\
  writeSuccessSourceBytes witness =
    take 720 (writeSuccessDecodedBytes witness) /\
  length (writeSuccessValues witness) = 74%nat /\
  bytes_of_u64s (writeSuccessValues witness) =
    take 592 (writeSuccessSourceBytes witness) /\
  bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 5) =
    Z.of_nat (length (writeSuccessPayload witness)) /\
  writeSuccessValueWord (writeSuccessValues witness) 7 =
    Z_to_bv 64 (writeSuccessTransactionBase witness) /\
  writeSuccessValueWord (writeSuccessValues witness) 8 =
    Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactions witness))) /\
  writeSuccessTransactionBytes witness =
    writeSuccessTransactionsBytes (writeSuccessTransactions witness) /\
  bv_unsigned (writeSuccessEntrySp witness) `mod` 16 = 0 /\
  (0x20000880 <= bv_unsigned (writeSuccessEntrySp witness))%Z /\
  (bv_unsigned (writeSuccessEntrySp witness) + 0x7d0 < 0x40000000)%Z.

(** The existing trace assertions describe output stores.  A later theorem must
    define this relation from those stores to the public byte string. *)
Definition WriteSuccessOutputRelation (Decoded : Type) : Type :=
  WriteSuccessArgs Decoded -> writeSuccessNativeWitness Decoded ->
  ByteString -> Prop.

Definition writeSuccessNativeAllows {State Decoded}
    (model : Level1MachineModel State Decoded) :
    WriteSuccessArgs Decoded -> ByteString -> Prop :=
  contractAllows State (WriteSuccessArgs Decoded) ByteString
    (writeSuccessContract model (fun _ => 0%nat)).

Lemma writeSuccessNativeAllows_exact {State Decoded}
    (model : Level1MachineModel State Decoded) args bytes :
  writeSuccessNativeAllows model args bytes <->
  decodeObservationSuccess State Decoded model bytes (successDecoded Decoded args).
Proof. reflexivity. Qed.

Definition writeSuccessTerminalSavedSlots `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  ((bv_unsigned (writeSuccessFrameSp witness) + 1992) ↦ₘ
     writeSuccessReturnValue witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1984) ↦ₘ
     writeSuccessSavedS0 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1976) ↦ₘ
     writeSuccessSavedS1 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1968) ↦ₘ
     writeSuccessSavedS2 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1960) ↦ₘ
     writeSuccessSavedS3 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1952) ↦ₘ
     writeSuccessSavedS4 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1944) ↦ₘ
     writeSuccessSavedS5 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1936) ↦ₘ
     writeSuccessSavedS6 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1928) ↦ₘ
     writeSuccessSavedS7 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1920) ↦ₘ
     writeSuccessSavedS8 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1912) ↦ₘ
     writeSuccessSavedS9 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1904) ↦ₘ
     writeSuccessSavedS10 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1896) ↦ₘ
     writeSuccessSavedS11 witness ∗ True)%I.

Definition writeSuccessTerminalMachine `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (writeSuccessReturnValue witness) ∗
   "x2" ↦ᵣ RVal_Bits (writeSuccessEntrySp witness) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessSavedS0 witness) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessSavedS1 witness) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessSavedS2 witness) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessSavedS3 witness) ∗
   "x20" ↦ᵣ RVal_Bits (writeSuccessSavedS4 witness) ∗
   "x21" ↦ᵣ RVal_Bits (writeSuccessSavedS5 witness) ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessSavedS6 witness) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessSavedS7 witness) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessSavedS8 witness) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessSavedS9 witness) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessSavedS10 witness) ∗
   "x27" ↦ᵣ RVal_Bits (writeSuccessSavedS11 witness) ∗
   writeSuccessTerminalSavedSlots witness)%I.

Definition writeSuccessTerminalResources `{!islaG Sigma} `{!threadG}
    {Decoded} (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) (bytes : ByteString) :
    iProp Sigma :=
  (∃ witness : writeSuccessNativeWitness Decoded,
    ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
    ⌜outputRelation args witness bytes⌝ ∗
    writeSuccessTerminalMachine witness)%I.

Definition writeSuccessHeaderTerminal `{!islaG Sigma} `{!threadG}
    {State Decoded} (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) : iProp Sigma :=
  (instr_pre 0x14d10
    (∃ bytes : ByteString,
      ⌜writeSuccessNativeAllows model args bytes⌝ ∗
      writeSuccessTerminalResources outputRelation args bytes))%I.

Definition writeSuccessLoadWithFramePre `{!islaG Sigma} `{!threadG}
    {State Decoded} (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    : iProp Sigma :=
  (instr_pre 0x14d80
    (writeSuccessAtLoadWithFrame
      (writeSuccessFrameSp witness)
      (writeSuccessSourceBytes witness)
      (writeSuccessCallerOutputEventsWithFrame
        (BV 64 0x179c5) (BV 64 6) (writeSuccessTraceTail witness))
      (writeSuccessLoadHeaderRemainder
        (writeSuccessHeaderTerminal model outputRelation args)
        (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness)
        (writeSuccessValues witness) (writeSuccessPayload witness)
        (writeSuccessTraceTail witness) (writeSuccessTransactionBase witness)
        (writeSuccessTransactions witness)
        (writeSuccessTransactionBytes witness))))%I.

Definition writeSuccessProloguePayload `{!islaG Sigma} `{!threadG}
    {State Decoded} (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    : iProp Sigma :=
  ((bv_unsigned (writeSuccessEntrySp witness) - 0x7d0) ↦ₘ? 1896 ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
     writeSuccessDecodedBytes witness ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessCallerOutputEventsWithFrame (BV 64 0x179c5) (BV 64 6)
     (writeSuccessTraceTail witness)) ∗
   writeSuccessLoadWithFramePre model outputRelation args witness ∗
   instr_pre 0x14d10 True ∗ True)%I.

Definition writeSuccessNativeEntry `{!islaG Sigma} `{!threadG}
    {State Decoded} (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) : iProp Sigma :=
  (∃ witness : writeSuccessNativeWitness Decoded,
    ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
    write_success_prologue_entry
      (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
      (writeSuccessReturnValue witness)
      (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
      (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
      (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
      (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
      (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
      (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
      (writeSuccessProloguePayload model outputRelation args witness))%I.

Definition writeSuccessNativeCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  writeSuccessCompleteNativeCode.

Definition writeSuccessNativeResources {State Decoded}
    (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    `{!islaG Sigma} `{!threadG} :
    IslarisContractResources (WriteSuccessArgs Decoded) ByteString := {|
  islarisCode := writeSuccessNativeCode;
  islarisEntry := writeSuccessNativeEntry model outputRelation;
  islarisExit := writeSuccessTerminalResources outputRelation
|}.

Definition writeSuccessNativeModel {State Decoded}
    (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (nextPc : Z -> Z -> Prop) :
    IslarisContractModel (WriteSuccessArgs Decoded) ByteString := {|
  islarisContractAllows := writeSuccessNativeAllows model;
  islarisContractStep := nextPc;
  islarisContractResources := fun Sigma HG HT =>
    @writeSuccessNativeResources State Decoded model outputRelation Sigma HG HT
|}.

(** A native correctness proof needs this semantic premise in addition to the
    machine-resource handoff and the CFG certificate. *)
Definition writeSuccessSemanticPremise {State Decoded}
    (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded) : Prop :=
  forall args witness bytes,
    writeSuccessWitnessWellFormed args witness ->
    outputRelation args witness bytes ->
    decodeObservationSuccess State Decoded model bytes (successDecoded Decoded args).
