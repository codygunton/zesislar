Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.

Import ListNotations.

Definition writeSuccessValueWord (values : list (bv 64)) (index : nat) :
    bv 64 := default (BV 64 0) (values !! index).

Definition writeSuccessValueEvents (sp : bv 64) (values : list (bv 64))
    (tail : spec) : spec :=
  writeOutputEventsAny (sp - 16)%bv (BV 64 8)
    (writeOutputEventsAny (sp - 16)%bv (BV 64 8)
      (writeOutputEventsAny (sp - 16)%bv (BV 64 8)
        (writeOutputEventsAny (sp - 16)%bv (BV 64 8)
          (writeOutputEventsAny (sp - 48)%bv (BV 64 8)
            (writeOutputEventsAny (writeSuccessValueWord values 4)
              (writeSuccessValueWord values 5)
              (writeOutputEventsAny (sp - 16)%bv (BV 64 8)
                (writeOutputEventsAny (sp + 1588)%bv (BV 64 32)
                (writeOutputEventsAny (sp - 16)%bv (BV 64 8) tail)))))))).

Definition writeSuccessValueRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessValueRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessValueRegisters.

Definition writeSuccessValuePost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessValueRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (default (BV 64 0) (values !! 8%nat)) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 0) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
   (bv_unsigned sp + 104) ↦ₘ default (BV 64 0) (values !! 7%nat) ∗
   (bv_unsigned sp + 112) ↦ₘ default (BV 64 0) (values !! 8%nat) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Definition writeSuccessValueSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHeaderRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 104) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
    bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessValueEvents sp values tail) ∗
    ⌜length values = 74%nat⌝ ∗
    ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    P ∗ instr_pre 0x14f04
      (writeSuccessValuePost sp values payload tail P))%I.


Local Instance : LithiumUnfold (@writeSuccessValueSpec) := I.
Local Instance : LithiumUnfold (@writeSuccessValuePost) := I.
