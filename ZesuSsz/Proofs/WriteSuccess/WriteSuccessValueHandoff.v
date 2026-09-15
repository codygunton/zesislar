Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.

Import ListNotations.

Definition writeSuccessValueHandoffRegisters : list string :=
  ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessValueHandoffRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
    writeSuccessValueHandoffRegisters.

Definition writeSuccessValueBaseFeeReturnSpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (b8 b9 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x14ed4) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
    "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp + 1588)%bv (BV 64 32)
        (writeOutputEventsAny (sp - 16)%bv (BV 64 8) tail)) ∗
    ("x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits b8 ∗ "x9" ↦ᵣ RVal_Bits b9 ∗
    (bv_unsigned sp - 48) ↦ₘ? 32 ∗
    reg_col writeSuccessValueHandoffRegShapes ∗
    (bv_unsigned sp + 104) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
    bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
    P ∗ instr_pre 0x14f04 (writeSuccessValuePost sp values payload tail P) ∗
    ⌜length values = 74%nat⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessValueBaseFeeReturnSpec) := I.

Ltac run_write_success_value_returns :=
  lazymatch goal with
  | |- environments.envs_entails _ ((_ -∗ _) ∗ True) =>
      iSplit; [|done];
      liARun;
      run_write_success_value_returns
  | |- environments.envs_entails _
      (subsume
        (instr ?address
          (IslaTraces.write_success_blocks.Index.lookup ?address)) _ _) =>
      iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]);
      iApply subsume_instr_some_pre;
      run_write_success_value_returns
  | _ => idtac
  end.
