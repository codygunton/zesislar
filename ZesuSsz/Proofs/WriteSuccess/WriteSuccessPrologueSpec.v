Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Import ListNotations.

Definition writeSuccessOtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7";
   "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessOtherRegisters.

Definition writeSuccessScratch `{!islaG Sigma} `{!threadG}
    (sp : bv 64) : iProp Sigma :=
  (∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : bv 64,
    (bv_unsigned sp - 0x68) ↦ₘ v0 ∗ (bv_unsigned sp - 0x60) ↦ₘ v1 ∗
    (bv_unsigned sp - 0x58) ↦ₘ v2 ∗ (bv_unsigned sp - 0x50) ↦ₘ v3 ∗
    (bv_unsigned sp - 0x48) ↦ₘ v4 ∗ (bv_unsigned sp - 0x40) ↦ₘ v5 ∗
    (bv_unsigned sp - 0x38) ↦ₘ v6 ∗ (bv_unsigned sp - 0x30) ↦ₘ v7 ∗
    (bv_unsigned sp - 0x28) ↦ₘ v8 ∗ (bv_unsigned sp - 0x20) ↦ₘ v9 ∗
    (bv_unsigned sp - 0x18) ↦ₘ v10 ∗ (bv_unsigned sp - 0x10) ↦ₘ v11 ∗
    (bv_unsigned sp - 0x8) ↦ₘ v12 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessScratch) := I.

Definition writeSuccessSavedSlots `{!islaG Sigma} `{!threadG}
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp - 0x68) ↦ₘ s11 ∗ (bv_unsigned sp - 0x60) ↦ₘ s10 ∗
   (bv_unsigned sp - 0x58) ↦ₘ s9 ∗ (bv_unsigned sp - 0x50) ↦ₘ s8 ∗
   (bv_unsigned sp - 0x48) ↦ₘ s7 ∗ (bv_unsigned sp - 0x40) ↦ₘ s6 ∗
   (bv_unsigned sp - 0x38) ↦ₘ s5 ∗ (bv_unsigned sp - 0x30) ↦ₘ s4 ∗
   (bv_unsigned sp - 0x28) ↦ₘ s3 ∗ (bv_unsigned sp - 0x20) ↦ₘ s2 ∗
   (bv_unsigned sp - 0x18) ↦ₘ s1 ∗ (bv_unsigned sp - 0x10) ↦ₘ s0 ∗
   (bv_unsigned sp - 0x8) ↦ₘ ra ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSavedSlots) := I.

Definition writeSuccessPrologueFacts `{!islaG Sigma} `{!threadG}
    (sp decoded : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (⌜bv_unsigned decoded = (bv_unsigned sp + 0x20)%Z⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(0x20000880 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 0x7d0 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessPrologueFacts) := I.

Definition write_success_prologue_entry `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits s0 ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
   "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
   "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
   "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
   "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
   "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
   "x10" ↦ᵣ RVal_Bits decoded ∗ "x11" ↦ᵣ: (fun _ =>
   "x12" ↦ᵣ: (fun _ =>
   writeSuccessScratch sp ∗ writeSuccessPrologueFacts sp decoded P)))%I.

Global Instance : LithiumUnfold (@write_success_prologue_entry) := I.

Definition writeSuccessPrologueRegisters `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits ((sp - BV 64 0x7d0)%bv) ∗
   "x8" ↦ᵣ RVal_Bits s0 ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
   "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
   "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
   "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
   "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
   "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
   "x10" ↦ᵣ RVal_Bits decoded ∗ "x11" ↦ᵣ: (fun _ =>
   "x12" ↦ᵣ: (fun _ => True)))%I.

Global Instance : LithiumUnfold (@writeSuccessPrologueRegisters) := I.

Definition writeSuccessPrologueAt14d48 `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ v4 v5 v6 v7 v8 v9 v10 v11 : bv 64,
   writeSuccessPrologueRegisters sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
     s8 s9 s10 s11 ∗
   (bv_unsigned sp - 0x68) ↦ₘ v11 ∗ (bv_unsigned sp - 0x60) ↦ₘ v10 ∗
   (bv_unsigned sp - 0x58) ↦ₘ v9 ∗ (bv_unsigned sp - 0x50) ↦ₘ v8 ∗
   (bv_unsigned sp - 0x48) ↦ₘ v7 ∗ (bv_unsigned sp - 0x40) ↦ₘ v6 ∗
   (bv_unsigned sp - 0x38) ↦ₘ v5 ∗ (bv_unsigned sp - 0x30) ↦ₘ v4 ∗
   (bv_unsigned sp - 0x28) ↦ₘ s3 ∗ (bv_unsigned sp - 0x20) ↦ₘ s2 ∗
   (bv_unsigned sp - 0x18) ↦ₘ s1 ∗ (bv_unsigned sp - 0x10) ↦ₘ s0 ∗
   (bv_unsigned sp - 0x8) ↦ₘ ra ∗ writeSuccessPrologueFacts sp decoded P)%I.

Global Instance : LithiumUnfold (@writeSuccessPrologueAt14d48) := I.

Definition writeSuccessPrologueAt14d5c `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ v9 v10 v11 : bv 64,
   writeSuccessPrologueRegisters sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
     s8 s9 s10 s11 ∗
   (bv_unsigned sp - 0x68) ↦ₘ v11 ∗ (bv_unsigned sp - 0x60) ↦ₘ v10 ∗
   (bv_unsigned sp - 0x58) ↦ₘ v9 ∗ (bv_unsigned sp - 0x50) ↦ₘ s8 ∗
   (bv_unsigned sp - 0x48) ↦ₘ s7 ∗ (bv_unsigned sp - 0x40) ↦ₘ s6 ∗
   (bv_unsigned sp - 0x38) ↦ₘ s5 ∗ (bv_unsigned sp - 0x30) ↦ₘ s4 ∗
   (bv_unsigned sp - 0x28) ↦ₘ s3 ∗ (bv_unsigned sp - 0x20) ↦ₘ s2 ∗
   (bv_unsigned sp - 0x18) ↦ₘ s1 ∗ (bv_unsigned sp - 0x10) ↦ₘ s0 ∗
   (bv_unsigned sp - 0x8) ↦ₘ ra ∗ writeSuccessPrologueFacts sp decoded P)%I.

Global Instance : LithiumUnfold (@writeSuccessPrologueAt14d5c) := I.

Definition write_success_prologue_exit `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0xfd78) ∗
   "x2" ↦ᵣ RVal_Bits ((sp - BV 64 0x7d0)%bv) ∗
   "x8" ↦ᵣ RVal_Bits decoded ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
   "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
   "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
   "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
   "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
   "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
   "x10" ↦ᵣ RVal_Bits ((sp - BV 64 0x698)%bv) ∗
   "x11" ↦ᵣ RVal_Bits decoded ∗ "x12" ↦ᵣ RVal_Bits (BV 64 720) ∗
   writeSuccessSavedSlots sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗
   P ∗ True)%I.

Global Instance : LithiumUnfold (@write_success_prologue_exit) := I.
