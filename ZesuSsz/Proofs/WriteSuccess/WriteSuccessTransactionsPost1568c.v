Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.

Definition writeSuccessTransactionsPost1568cAddiSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (∃ sp : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x18" ↦ᵣ: (fun _ => True) ∗
    instr_pre (pc + 4)
      (reg_col zesu_ram_sys_regs ∗
       "x2" ↦ᵣ RVal_Bits sp ∗
       "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost1568cAddiSpec) := I.

Lemma write_success_transactions_post_1568c_addi_spec
    `{!islaG Sigma} `{!threadG} (pc : Z) :
  instr pc (Some IslaTraces.write_success_89.a1568c.a1568c) -∗
  instr_body pc (writeSuccessTransactionsPost1568cAddiSpec pc).
Proof. move => *. zesu_block. Qed.

Lemma write_success_transactions_post_1568c_addi
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15690
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P) -∗
  instr_body 0x1568c
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x18" ↦ᵣ: (fun _ => True) ∗ P).
Proof. move => *. zesu_block. Qed.
