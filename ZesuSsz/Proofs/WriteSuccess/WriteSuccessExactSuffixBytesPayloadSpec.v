Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessOutputSemantic WriteSuccessObservation WriteSuccessExactSuffixBytesPayload158e0.
Import ListNotations.
Open Scope Z_scope.

Definition exactSuffixBytesPayloadFrame `{!islaG Sigma} `{!threadG}
    (dataOffset sizeOffset : Z) (sp data size : bv 64)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      exactSuffixBytesOtherRegisters) ∗
   (bv_unsigned sp + dataOffset) ↦ₘ data ∗
   (bv_unsigned sp + sizeOffset) ↦ₘ size ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactSuffixBytesPayloadFrame) := I.

Definition exactSuffixBytesPayloadEntryRegisters `{!islaG Sigma} `{!threadG}
    (sp oldS0 oldS1 : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x1"; "x5"; "x6"; "x10"; "x11"]) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits oldS0 ∗
   "x9" ↦ᵣ RVal_Bits oldS1)%I.
Global Instance : LithiumUnfold (@exactSuffixBytesPayloadEntryRegisters) := I.

Definition exactSuffixBytesPayloadEntryAt `{!islaG Sigma} `{!threadG}
    (dataOffset sizeOffset : Z) (sp data size oldS0 oldS1 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (exactSuffixBytesPayloadEntryRegisters sp oldS0 oldS1 ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
      (writeOutputEvents data size bytes tail)) ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes /\
      bv_unsigned sp `mod` 16 = 0 /\
      mapRamBase defaultMap <= bv_unsigned sp - 48 /\
      bv_unsigned sp < machineRamEnd defaultMap /\
      bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗
    exactSuffixBytesPayloadFrame dataOffset sizeOffset sp data size bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@exactSuffixBytesPayloadEntryAt) := I.

Definition exactSuffixBytesPayloadEntry `{!islaG Sigma} `{!threadG}
    (dataOffset sizeOffset : Z) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (tail : spec),
    exactSuffixBytesPayloadEntryAt dataOffset sizeOffset sp data size oldS0 oldS1 bytes tail P)%I.
Global Instance : LithiumUnfold (@exactSuffixBytesPayloadEntry) := I.

Definition exactSuffixBytesPayloadReturnRegisters `{!islaG Sigma} `{!threadG}
    (returnPc sp data size oldS0 oldS1 : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits returnPc ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   reg_col [(KindReg "x6", BitsShape 64)] ∗
   "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size)%I.
Global Instance : LithiumUnfold (@exactSuffixBytesPayloadReturnRegisters) := I.

Definition exactSuffixBytesPayloadReturnAt `{!islaG Sigma} `{!threadG}
    (returnPc : bv 64) (dataOffset sizeOffset : Z) (sp data size oldS0 oldS1 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (exactSuffixBytesPayloadReturnRegisters returnPc sp data size oldS0 oldS1 ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0 /\
      mapRamBase defaultMap <= bv_unsigned sp - 48 /\
      bv_unsigned sp < machineRamEnd defaultMap /\
      bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗
    exactSuffixBytesPayloadFrame dataOffset sizeOffset sp data size bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@exactSuffixBytesPayloadReturnAt) := I.

Definition exactSuffixBytesPayloadReturn `{!islaG Sigma} `{!threadG}
    (returnPc : bv 64) (dataOffset sizeOffset : Z) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (tail : spec),
    exactSuffixBytesPayloadReturnAt returnPc dataOffset sizeOffset sp data size oldS0 oldS1 bytes tail P)%I.
Global Instance : LithiumUnfold (@exactSuffixBytesPayloadReturn) := I.
