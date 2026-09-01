From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Experiments.WriteSuccessLoopCommon.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Fixpoint writeSuccessStorageKeysEvents (sp : bv 64) (count : nat)
    (tail : spec) : spec :=
  match count with
  | O => tail
  | S count =>
      writeOutputEvents (sp + BV 64 1712)%bv (BV 64 32)
        (writeSuccessStorageKeysEvents sp count tail)
  end.

Definition writeSuccessStorageKeysOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x23"; "x24"; "x25"; "x26";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessStorageKeysOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessStorageKeysOtherRegisters.

Definition writeSuccessStorageKeysScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  (∃ word0 word1 word2 word3 : bv 64,
    (bv_unsigned sp + 1712) ↦ₘ word0 ∗
    (bv_unsigned sp + 1720) ↦ₘ word1 ∗
    (bv_unsigned sp + 1728) ↦ₘ word2 ∗
    (bv_unsigned sp + 1736) ↦ₘ word3 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysScratch) := I.

Definition writeSuccessStorageKeysLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ pointer : bv 64,
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessStorageKeysOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x22" ↦ᵣ RVal_Bits pointer ∗
    "x27" ↦ᵣ RVal_Bits (BV 64 0) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessStorageKeysScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat total)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysLoopExit) := I.

Definition writeSuccessStorageKeysLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessStorageKeysOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x22" ↦ᵣ RVal_Bits pointer ∗
    "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessStorageKeysScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessStorageKeysEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x153b4
      (writeSuccessStorageKeysLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysLoopSpec) := I.

Definition writeSuccessStorageKeysTailSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessStorageKeysOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x22" ↦ᵣ RVal_Bits pointer ∗
    "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessStorageKeysScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessStorageKeysEvents sp remaining tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x153b4
      (writeSuccessStorageKeysLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysTailSpec) := I.

Ltac prove_write_success_storage_segment boundary :=
  prove_write_success_blob_segment boundary;
  liARun;
  lazymatch goal with
  | [ tail : spec, bytes : list (bv 8), processed : nat,
      remaining : nat, base : Z |- _ ] =>
      iExists
        (tail, bytes, processed,
         (processed + S remaining)%nat, base, tt)ₗ
  end;
  liARun.

Ltac solve_write_success_storage_obligation :=
  prepare_sidecond;
  try (apply bv_eq; rewrite bv_and_unsigned; assumption);
  try (bv_simplify_arith H1; bv_solve).
