From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_monolithic_00 Require Import instrs.
From IslaTraces.write_success_monolithic_01 Require Import instrs.
From IslaTraces.write_success_monolithic_02 Require Import instrs.
From IslaTraces.write_success_monolithic_03 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

Import ListNotations.

Definition writeSuccessMonolithicOtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessMonolithicOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessMonolithicOtherRegisters.

(** This deliberately uses one [instr_body] and one automation run.  It does
    not import, state, or apply contracts for any callee.  [Abort] keeps the
    first direct-search result visible without presenting it as a proof. *)
Lemma write_success_monolithic_attempt `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (tail : spec) :
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_00.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14d30 (
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessMonolithicOtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits s0 ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
    "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
    "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
    "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
    "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
    "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
    "x10" ↦ᵣ RVal_Bits decoded ∗ "x11" ↦ᵣ: (fun _ =>
    "x12" ↦ᵣ: (fun _ =>
    (bv_unsigned sp - 0x7d0) ↦ₘ? 2000 ∗
    bv_unsigned decoded ↦ₘ? 2000 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace tail ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜(0x20000800 <= bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 0x800 < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 3 decoded = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned decoded)%Z⌝ ∗
    ⌜(bv_unsigned decoded + 2000 < 0x40000000)%Z⌝ ∗
    instr_pre 0x14d10 True ∗ True)))%I.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Show.
Abort.
