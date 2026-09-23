Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_116 Require Import a15964.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixInt15968Call.

Definition writeSuccessSuffixInt15964HandoffSpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    instr_pre 0x15968 (writeSuccessSuffixInt15968CallSpec Q) ∗
    instr_pre 0x1596c (writeSuccessSuffixInt1596cCallPost sp tail ∗ Q) ∗
    Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt15964HandoffSpec) := I.

Lemma write_success_suffix_int_15964_handoff
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr 0x15964 (Some IslaTraces.write_success_116.a15964.a15964) -∗
  instr_body 0x15964 (writeSuccessSuffixInt15964HandoffSpec Q).
Proof. move => *. zesu_block. Qed.
