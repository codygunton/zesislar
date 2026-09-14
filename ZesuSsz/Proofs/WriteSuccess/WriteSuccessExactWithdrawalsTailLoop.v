Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsTailBranches
  WriteSuccessExactWithdrawalsTailPositive WriteSuccessExactWithdrawalsTailZero
  WriteSuccessExactWithdrawalsReturnFacts.
Global Instance : LithiumUnfold (@withdrawalLoopFacts) := I.

Lemma withdrawal_tail_loop_correct `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) base rows prefix row rest source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_95.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15694 (withdrawalLoopSpec sp base rows source tail P) -∗
  instr_body 0x156dc (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
    withdrawalTailPayload sp pointer base rows prefix row rest source tail P ∗ True)%I.
Proof.
  destruct rest as [|next rest].
  - zesu_block.
    all: try reflexivity.
    exact (withdrawal_facts_end_pointer sp pointer base rows prefix row source H0).
  - zesu_block.
    1,2: exfalso; have Hbound := (proj1 (proj2 (proj2 (proj2 (proj2 H0)))));
      have Hzero := zesu_counter_zero_z_bound (S (length rest)) ltac:(cbn in Hbound; lia) H4;
      discriminate.
    liInst (fun x => x.1ₗ = next /\ x.2ₗ = prefix ++ [row]).
    zesu_run.
    exact (withdrawal_facts_advance sp pointer base rows prefix row next rest source H0).
Qed.
Print Assumptions withdrawal_tail_loop_correct.

