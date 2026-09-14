Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Record writeSuccessAccessEntry := {
  writeSuccessAccessEntryBytes : list (bv 8);
  writeSuccessAccessEntryStoragePointer : bv 64;
  writeSuccessAccessEntryStorageCount : nat;
  writeSuccessAccessEntryStorageBytes : list (bv 8);
}.

Definition writeSuccessAccessEntryWord
    (entry : writeSuccessAccessEntry) (offset : nat) : bv 64 :=
  Z_to_bv 64
    (little_endian_to_bv 8
      (take 8 (drop offset (writeSuccessAccessEntryBytes entry)))).

Definition writeSuccessAccessEntryValid
    (entry : writeSuccessAccessEntry) : Prop :=
  length (writeSuccessAccessEntryBytes entry) = 40%nat /\
  writeSuccessAccessEntryWord entry 0 =
    writeSuccessAccessEntryStoragePointer entry /\
  writeSuccessAccessEntryWord entry 8 =
    Z_to_bv 64 (Z.of_nat (writeSuccessAccessEntryStorageCount entry)) /\
  length (writeSuccessAccessEntryStorageBytes entry) =
    (32 * writeSuccessAccessEntryStorageCount entry)%nat /\
  (writeSuccessAccessEntryStorageCount entry < 2 ^ 64)%nat.

Definition writeSuccessAccessEntryStorageOwn `{!islaG Sigma}
    (entry : writeSuccessAccessEntry) : iProp Sigma :=
  match writeSuccessAccessEntryStorageCount entry with
  | O => True
  | S _ =>
      (bv_unsigned (writeSuccessAccessEntryStoragePointer entry) ↦ₘ∗
        writeSuccessAccessEntryStorageBytes entry ∗
       ⌜(mapRamBase defaultMap) <=
         bv_unsigned (writeSuccessAccessEntryStoragePointer entry)⌝ ∗
       ⌜bv_unsigned (writeSuccessAccessEntryStoragePointer entry) +
         Z.of_nat (length (writeSuccessAccessEntryStorageBytes entry)) <
         (machineRamEnd defaultMap)⌝ ∗ True)%I
  end.

Global Instance writeSuccessAccessEntryStorageOwn_unfold :
    LithiumUnfold (@writeSuccessAccessEntryStorageOwn) := I.

Definition writeSuccessAccessEntryOwn `{!islaG Sigma}
    (entry : writeSuccessAccessEntry) : iProp Sigma :=
  (writeSuccessAccessEntryStorageOwn entry ∗
   ⌜writeSuccessAccessEntryValid entry⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessEntryOwn) := I.

Fixpoint writeSuccessAccessEntriesOwn `{!islaG Sigma}
    (entries : list writeSuccessAccessEntry) : iProp Sigma :=
  match entries with
  | [] => True
  | entry :: entries =>
      (writeSuccessAccessEntryOwn entry ∗
       writeSuccessAccessEntriesOwn entries ∗ True)%I
  end.

Global Instance : LithiumUnfold (@writeSuccessAccessEntriesOwn) := I.

Fixpoint writeSuccessAccessEntriesBytes
    (entries : list writeSuccessAccessEntry) : list (bv 8) :=
  match entries with
  | [] => []
  | entry :: entries =>
      writeSuccessAccessEntryBytes entry ++
      writeSuccessAccessEntriesBytes entries
  end.

Fixpoint writeSuccessAccessListsEvents (sp : bv 64)
    (entries : list writeSuccessAccessEntry) (tail : spec) : spec :=
  match entries with
  | [] => tail
  | entry :: entries =>
      writeOutputEventsAny (sp + BV 64 1760)%bv (BV 64 20)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessStorageKeysEvents sp
            (writeSuccessAccessEntryStorageCount entry)
            (writeSuccessAccessListsEvents sp entries tail)))
  end.

Inductive writeSuccessAccessListsPhase :=
  | AccessListsOutput
  | AccessListsCount
  | AccessListsStorage.

Definition writeSuccessAccessListsPhaseEvents
    (phase : writeSuccessAccessListsPhase) (sp : bv 64)
    (entry : writeSuccessAccessEntry)
    (remaining : list writeSuccessAccessEntry) (tail : spec) : spec :=
  match phase with
  | AccessListsOutput =>
      writeOutputEventsAny (sp + BV 64 1760)%bv (BV 64 20)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessStorageKeysEvents sp
            (writeSuccessAccessEntryStorageCount entry)
            (writeSuccessAccessListsEvents sp remaining tail)))
  | AccessListsCount =>
      writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessStorageKeysEvents sp
          (writeSuccessAccessEntryStorageCount entry)
          (writeSuccessAccessListsEvents sp remaining tail))
  | AccessListsStorage =>
      writeSuccessStorageKeysEvents sp
        (writeSuccessAccessEntryStorageCount entry)
        (writeSuccessAccessListsEvents sp remaining tail)
  end.

Definition writeSuccessAccessListsOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18";
   "x20"; "x21"; "x23"; "x24"; "x25"; "x26"; "x28"; "x29";
   "x30"; "x31"].

Definition writeSuccessAccessListsOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessAccessListsOtherRegisters.

Definition writeSuccessAccessListsScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total : nat)
    (storedIndex savedX22 : bv 64) :
    iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ savedX22 ∗
    (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
    (bv_unsigned sp + 272) ↦ₘ storedIndex ∗
    (bv_unsigned sp + 1744) ↦ₘ? 40 ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    writeSuccessStorageKeysScratch sp ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsScratch) := I.

Definition writeSuccessAccessListsCopiedScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total processed : nat)
    (entry : writeSuccessAccessEntry) (savedX22 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ savedX22 ∗
    (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
    (bv_unsigned sp + 272) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
    (bv_unsigned sp + 1744) ↦ₘ∗ writeSuccessAccessEntryBytes entry ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    writeSuccessStorageKeysScratch sp ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsCopiedScratch) := I.

Definition writeSuccessAccessListsInvariant `{!islaG Sigma}
    (sp : bv 64) (base : Z)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes prefix suffix : list (bv 8)) : iProp Sigma :=
  (⌜entries = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜prefix = writeSuccessAccessEntriesBytes processed⌝ ∗
   ⌜suffix = writeSuccessAccessEntriesBytes remaining⌝ ∗
   ⌜bytes = prefix ++ suffix⌝ ∗
   ⌜length bytes = (40 * length entries)%nat⌝ ∗
   ⌜length prefix = (40 * length processed)%nat⌝ ∗
   ⌜length suffix = (40 * length remaining)%nat⌝ ∗
   ⌜(length entries < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜entries <> [] -> (mapRamBase defaultMap) <= base⌝ ∗
   ⌜entries <> [] ->
      base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsInvariant) := I.

Definition writeSuccessAccessListsLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (tail : spec) (x19 savedX22 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (storedIndex x22 x27 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x19" ↦ᵣ RVal_Bits x19 ∗
    "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length entries))) ∗
    "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length entries))) ∗
    "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
    base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
    writeSuccessAccessListsScratch
      sp base (length entries) storedIndex savedX22 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsLoopExit) := I.

Definition writeSuccessAccessListsLoopSpec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (storedIndex savedX22 x10 x22 x27 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits x10 ∗
    "x19" ↦ᵣ RVal_Bits x19 ∗
    "x11" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length processed))) ∗
    "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
    base ↦ₘ∗ prefix ∗
    (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessEntriesOwn remaining ∗
    writeSuccessAccessListsScratch
      sp base (length entries) storedIndex savedX22 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessAccessListsEvents sp remaining tail) ∗ P ∗
    writeSuccessAccessListsInvariant
      sp base entries processed remaining bytes prefix suffix ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit
        sp base entries bytes tail x19 savedX22 P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsLoopSpec) := I.

Definition writeSuccessAccessListsCopiedSpec `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessAccessListsPhase) (x19 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (savedX22 x10 x11 x22 x27 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits x10 ∗
    "x19" ↦ᵣ RVal_Bits x19 ∗
    "x11" ↦ᵣ RVal_Bits x11 ∗
    "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
    base ↦ₘ∗ prefix ∗
    (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessEntriesOwn (entry :: remaining) ∗
    writeSuccessAccessListsCopiedScratch
      sp base (length entries) (length processed) entry savedX22 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeSuccessAccessListsPhaseEvents phase sp entry remaining tail) ∗ P ∗
    writeSuccessAccessListsInvariant
      sp base entries processed (entry :: remaining) bytes prefix suffix ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit
        sp base entries bytes tail x19 savedX22 P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsCopiedSpec) := I.

Definition writeSuccessAccessListsTailSpec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (savedX22 x10 x11 x22 x27 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits x10 ∗
    "x19" ↦ᵣ RVal_Bits x19 ∗
    "x11" ↦ᵣ RVal_Bits x11 ∗
    "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
    base ↦ₘ∗ prefix ∗
    (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessAccessEntriesOwn processed ∗
    writeSuccessAccessEntriesOwn (entry :: remaining) ∗
    writeSuccessAccessListsScratch sp base (length entries)
      (Z_to_bv 64 (Z.of_nat (length processed))) savedX22 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessAccessListsEvents sp remaining tail) ∗ P ∗
    writeSuccessAccessListsInvariant
      sp base entries processed (entry :: remaining) bytes prefix suffix ∗
    instr_pre 0x153c0
      (writeSuccessAccessListsLoopExit
        sp base entries bytes tail x19 savedX22 P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAccessListsTailSpec) := I.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Ltac run_write_success_access_lists_chunk boundary :=
  lazymatch goal with
  | |- instr_body boundary _ => idtac
  | |- environments.envs_entails _ (⌜_⌝)%I =>
      prepare_sidecond;
      run_write_success_access_lists_chunk boundary
  | _ =>
      first
        [ progress iEval (unfold zesuMemcpyCallSpec, zesu_c_call)
        | progress iEval (unfold zesuEncoderIntCallSpec, zesu_c_call)
        | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | progress unfold LET_ID
        | progress unfold TRACE_LET
        | progress unLET
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | apply bv_eq; rewrite bv_and_unsigned; assumption
        | bv_solve
        | lia ];
      run_write_success_access_lists_chunk boundary
  end.

Ltac run_write_success_access_lists_return boundary :=
  lazymatch goal with
  | |- environments.envs_entails _ (∃ _ : (), _)%I =>
      iExists tt;
      iSplit; [|done];
      run_write_success_access_lists_chunk boundary;
      run_write_success_access_lists_return boundary
  | |- environments.envs_entails _ ((_ -∗ _) ∗ True) =>
      iSplit; [|done];
      liARun;
      run_write_success_access_lists_return boundary
  | |- environments.envs_entails _
      (subsume
        (instr ?address
          (IslaTraces.write_success_blocks.Index.lookup ?address)) _ _) =>
      iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]);
      iApply subsume_instr_some_pre;
      run_write_success_access_lists_return boundary
  | _ => idtac
  end.
