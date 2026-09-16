Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Continuations.
Require Import isla.riscv64.riscv64.

Lemma test_instr_body_exists `{!islaG Sigma} `{!threadG} (pc : Z) :
  (∀ value : bv 64, instr_body pc
    (reg_col sys_regs ∗ "x10" ↦ᵣ RVal_Bits value ∗ True)) -∗
  instr_body pc (∃ value : bv 64,
    reg_col sys_regs ∗ "x10" ↦ᵣ RVal_Bits value ∗ True).
Proof. iStartProof. iApply instr_body_exists. Qed.
Print Assumptions test_instr_body_exists.
