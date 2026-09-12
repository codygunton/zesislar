Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma test_block_reduces_code_list `{!islaG Sigma} `{!threadG} (sp : bv 64) :
  ([∗ list] instruction ∈ take 1 IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4
    (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     instr_pre 0x15ce8
       (reg_col zesu_ram_sys_regs ∗
        "x2" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗ True) ∗ True).
Proof. zesu_block. Qed.

Print Assumptions test_block_reduces_code_list.

Lemma test_body_to_pre_subsumption `{!islaG Sigma} `{!threadG}
    (address : Z) (sp : bv 64) :
  ⊢ subsume (instr_body address ("x2" ↦ᵣ RVal_Bits sp ∗ True))
    (fun _ : unit => instr_pre address ("x2" ↦ᵣ RVal_Bits sp ∗ True))
    (fun _ => True%I).
Proof.
  iStartProof. liARun.
  Unshelve. all: prepare_sidecond; try reflexivity.
Qed.

Print Assumptions test_body_to_pre_subsumption.
