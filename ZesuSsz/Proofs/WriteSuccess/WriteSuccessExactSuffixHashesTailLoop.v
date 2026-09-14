Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesLoopSpec WriteSuccessExactSuffixHashesReturnFacts.
From IslaTraces.write_success_107 Require Import instrs.
Global Instance : LithiumUnfold (@suffixLoopFacts) := I.

Lemma suffix_tail_loop_correct `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) base total processed remaining source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_107.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15754 (suffixLoopSpec sp base total source tail P) -∗
  instr_body 0x158d4 (reg_col zesu_ram_sys_regs ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    suffixTailPayload sp pointer base total processed remaining source tail P ∗ True)%I.
Proof.
  destruct remaining as [|remaining].
  - zesu_block.
    all: try reflexivity.
    exact (suffix_facts_end_pointer sp pointer base total processed source H0).
  - zesu_block.
    1,2: exfalso; have Hbound := (proj1 (proj2 (proj2 (proj2 H0))));
      have Hzero := zesu_counter_zero_z_bound (S remaining) ltac:(cbn in Hbound; lia) H4;
      discriminate.
    liInst (fun x => x.1ₗ = S processed).
    zesu_run.
    eapply suffix_facts_advance. exact H0.
Qed.
Print Assumptions suffix_tail_loop_correct.
