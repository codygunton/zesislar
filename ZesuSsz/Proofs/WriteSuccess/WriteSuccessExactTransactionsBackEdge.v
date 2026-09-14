Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_86 Require Import instrs.
From IslaTraces.write_success_28 Require Import instrs.
Local Remove Hints IslaTraces.write_success_86.a1565c_spec.a1565c_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_28.a14f00_spec.a14f00_spec_inst : typeclass_instances.

Definition transactionBackEdgePost `{!islaG Sigma} `{!threadG}
    (sp index total : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits total ∗ "x11" ↦ᵣ RVal_Bits (index + BV 64 1)%bv ∗
   (bv_unsigned sp + 112) ↦ₘ total ∗ (bv_unsigned sp + 248) ↦ₘ index ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 256 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionBackEdgePost) := I.

Definition transactionBackEdgeEntry `{!islaG Sigma} `{!threadG}
    (sp index total : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] ∗
   (bv_unsigned sp + 112) ↦ₘ total ∗ (bv_unsigned sp + 248) ↦ₘ index ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 256 < 0x40000000⌝ ∗ P ∗
   instr_pre 0x14f04 (transactionBackEdgePost sp index total P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionBackEdgeEntry) := I.

Lemma transactions_back_edge_correct `{!islaG Sigma} `{!threadG}
    sp index total (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_86.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr 0x14f00 (Some IslaTraces.write_success_28.a14f00.a14f00) -∗
  instr_body 0x1565c (transactionBackEdgeEntry sp index total P).
Proof. zesu_block. Qed.
Print Assumptions transactions_back_edge_correct.
