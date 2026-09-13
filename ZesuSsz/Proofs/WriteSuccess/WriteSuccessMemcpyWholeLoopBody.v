Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayCopyFinish.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_02 Require Import instrs.
Local Open Scope Z_scope.

Definition memcpyWholeLoopSpec `{!islaG Sigma} `{!threadG}
    (base : Z) (start : nat) (source : list (bv 8))
    (src dst n ret : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (i tmp13 tmp14 : bv 64) (data : list (bv 8)),
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
   "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
   "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
   "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits i ∗
   base ↦ₘ∗ source ∗ bv_unsigned dst ↦ₘ∗ data ∗
   ⌜bv_unsigned src = (base + Z.of_nat start)%Z⌝ ∗
   ⌜bv_unsigned n = Z.of_nat (length data)⌝ ∗
   ⌜(start + length data <= length source)%nat⌝ ∗
   ⌜(bv_unsigned i <= bv_unsigned n)%Z⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length source) < 0x40000000)%Z⌝ ∗
   ⌜(0x20000000 <= bv_unsigned dst)%Z⌝ ∗ ⌜(bv_unsigned dst + bv_unsigned n < 0x40000000)%Z⌝ ∗
   ⌜take (Z.to_nat (bv_unsigned i)) data =
     take (Z.to_nat (bv_unsigned i)) (drop start source)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
   instr_pre (bv_unsigned ret)
     (∃ final13 final14 : bv 64,
      reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
      "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
      "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits final13 ∗
      "x14" ↦ᵣ RVal_Bits final14 ∗ "x15" ↦ᵣ RVal_Bits n ∗
      base ↦ₘ∗ source ∗ bv_unsigned dst ↦ₘ∗ take (Z.to_nat (bv_unsigned n)) (drop start source) ∗
      P ∗ True) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@memcpyWholeLoopSpec) := I.

Lemma memcpy_whole_loop_body `{!islaG Sigma} `{!threadG}
    base start source src dst n ret (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d8 (memcpyWholeLoopSpec base start source src dst n ret P) -∗
  instr_body 0x101d8 (memcpyWholeLoopSpec base start source src dst n ret P).
Proof. zesu_block. all: zesu_copy_finish. Qed.
Print Assumptions memcpy_whole_loop_body.
