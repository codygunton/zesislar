Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsWithdrawalsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopMemory.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Fixpoint writeSuccessWithdrawalsEvents (sp : bv 64) (count : nat)
    (tail : spec) : spec :=
  match count with
  | O => tail
  | S count =>
      writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeOutputEventsAny (sp + BV 64 1768)%bv (BV 64 20)
            (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
              (writeSuccessWithdrawalsEvents sp count tail))))
  end.

Inductive writeSuccessWithdrawalsPhase :=
  | WithdrawalsFirstInt
  | WithdrawalsSecondInt
  | WithdrawalsOutput
  | WithdrawalsThirdInt
  | WithdrawalsTail.

Definition writeSuccessWithdrawalsPhaseEvents
    (phase : writeSuccessWithdrawalsPhase) (sp : bv 64)
    (remaining : nat) (tail : spec) : spec :=
  match phase with
  | WithdrawalsFirstInt => writeSuccessWithdrawalsEvents sp (S remaining) tail
  | WithdrawalsSecondInt =>
      writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeOutputEventsAny (sp + BV 64 1768)%bv (BV 64 20)
          (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
            (writeSuccessWithdrawalsEvents sp remaining tail)))
  | WithdrawalsOutput =>
      writeOutputEventsAny (sp + BV 64 1768)%bv (BV 64 20)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessWithdrawalsEvents sp remaining tail))
  | WithdrawalsThirdInt =>
      writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessWithdrawalsEvents sp remaining tail)
  | WithdrawalsTail => writeSuccessWithdrawalsEvents sp remaining tail
  end.

Definition writeSuccessWithdrawalsOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
   "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessWithdrawalsOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessWithdrawalsOtherRegisters.

Definition writeSuccessWithdrawalsScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsScratch) := I.

Definition writeSuccessWithdrawalsCopiedScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  (∃ current : list (bv 8),
    (bv_unsigned sp + 1744) ↦ₘ∗ current ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    ⌜length current = 48%nat⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsCopiedScratch) := I.

Definition writeSuccessWithdrawalsInvariant `{!islaG Sigma}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes prefix suffix : list (bv 8)) : iProp Sigma :=
  (⌜total = (processed + S remaining)%nat⌝ ∗
   ⌜length bytes = (48 * total)%nat⌝ ∗
   ⌜bytes = prefix ++ suffix⌝ ∗
   ⌜length prefix = (48 * processed)%nat⌝ ∗
   ⌜length suffix = (48 * S remaining)%nat⌝ ∗
   ⌜bv_unsigned pointer = (base + 48 * Z.of_nat processed)%Z⌝ ∗
   ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp - 16)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsInvariant) := I.

Definition writeSuccessWithdrawalsLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ pointer : bv 64,
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗
    "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
    base ↦ₘ∗ bytes ∗ writeSuccessWithdrawalsScratch sp ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗
    ⌜bv_unsigned pointer = (base + 48 * Z.of_nat total)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsLoopExit) := I.

Definition writeSuccessWithdrawalsLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
    base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
    writeSuccessWithdrawalsScratch sp ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessWithdrawalsEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessWithdrawalsInvariant
      sp pointer base total processed remaining bytes prefix suffix ∗
    instr_pre 0x156e8
      (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsLoopSpec) := I.

Definition writeSuccessWithdrawalsCopiedSpec `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessWithdrawalsPhase) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
    base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
    writeSuccessWithdrawalsCopiedScratch sp ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessWithdrawalsPhaseEvents phase sp remaining tail) ∗ P ∗
    writeSuccessWithdrawalsInvariant
      sp pointer base total processed remaining bytes prefix suffix ∗
    instr_pre 0x156e8
      (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsCopiedSpec) := I.

Definition writeSuccessWithdrawalsTailSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
    base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
    writeSuccessWithdrawalsScratch sp ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessWithdrawalsEvents sp remaining tail) ∗ P ∗
    writeSuccessWithdrawalsInvariant
      sp pointer base total processed remaining bytes prefix suffix ∗
    instr_pre 0x156e8
      (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsTailSpec) := I.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Ltac run_write_success_withdrawals_chunk boundary :=
  lazymatch goal with
  | |- instr_body boundary _ => idtac
  | |- environments.envs_entails _ (⌜_⌝)%I =>
      prepare_sidecond;
      run_write_success_withdrawals_chunk boundary
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
      run_write_success_withdrawals_chunk boundary
  end.
