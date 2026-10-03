Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Import ListNotations.

Definition writeSuccessHeaderRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessHeaderRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessHeaderRegisters.

Definition writeSuccessHeaderEvent (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data)
    (scons (SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size) tail).

Definition writeSuccessHeaderEvents (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (BV 64 0x179c5) (BV 64 6)
    (writeSuccessHeaderEvent (sp + 1184)%bv (BV 64 32)
      (writeSuccessHeaderEvent (sp + 1216)%bv (BV 64 20)
        (writeSuccessHeaderEvent (sp + 1236)%bv (BV 64 32)
          (writeSuccessHeaderEvent (sp + 1268)%bv (BV 64 32)
            (writeSuccessHeaderEvent (sp + 1300)%bv (BV 64 256)
              (writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32)
                tail)))))).

Definition writeSuccessHeaderEventsAfterTag (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (sp + 1184)%bv (BV 64 32)
    (writeSuccessHeaderEvent (sp + 1216)%bv (BV 64 20)
      (writeSuccessHeaderEvent (sp + 1236)%bv (BV 64 32)
        (writeSuccessHeaderEvent (sp + 1268)%bv (BV 64 32)
          (writeSuccessHeaderEvent (sp + 1300)%bv (BV 64 256)
            (writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32) tail))))).

Definition writeSuccessHeaderEventsAfter1184 (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (sp + 1216)%bv (BV 64 20)
    (writeSuccessHeaderEvent (sp + 1236)%bv (BV 64 32)
      (writeSuccessHeaderEvent (sp + 1268)%bv (BV 64 32)
        (writeSuccessHeaderEvent (sp + 1300)%bv (BV 64 256)
          (writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32) tail)))).

Definition writeSuccessHeaderEventsAfter1216 (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (sp + 1236)%bv (BV 64 32)
    (writeSuccessHeaderEvent (sp + 1268)%bv (BV 64 32)
      (writeSuccessHeaderEvent (sp + 1300)%bv (BV 64 256)
        (writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32) tail))).

Definition writeSuccessHeaderEventsAfter1236 (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (sp + 1268)%bv (BV 64 32)
    (writeSuccessHeaderEvent (sp + 1300)%bv (BV 64 256)
      (writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32) tail)).

Definition writeSuccessHeaderEventsAfter1268 (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (sp + 1300)%bv (BV 64 256)
    (writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32) tail).

Definition writeSuccessHeaderEventsAfter1300 (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32) tail.

Definition writeSuccessHeaderPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ P ∗ True)%I.

Definition writeSuccessHeaderBeforeCopySpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (events tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ? 864 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace events ∗
   ⌜length bytes = 720%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x14e88 (writeSuccessHeaderPost sp bytes tail P) ∗ True)%I.

Definition writeSuccessHeaderAfterCopySpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (events tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace events ∗
   ⌜length bytes = 720%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x14e88 (writeSuccessHeaderPost sp bytes tail P) ∗ True)%I.

Definition writeSuccessHeaderSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (bytes : list (bv 8)) (tail : spec),
    writeSuccessHeaderBeforeCopySpec sp bytes
      (writeSuccessHeaderEvents sp tail) tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessHeaderSpec) := I.
Global Instance : LithiumUnfold (@writeSuccessHeaderPost) := I.
Global Instance : LithiumUnfold (@writeSuccessHeaderBeforeCopySpec) := I.
Global Instance : LithiumUnfold (@writeSuccessHeaderAfterCopySpec) := I.
