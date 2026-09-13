Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTail.
Require Import isla.riscv64.riscv64.

Lemma access_lists_tail_guarded_correct `{!islaG Sigma} `{!threadG}
    sp index old11 (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_63.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_pre 0x151d4 (accessListsTailPost sp index P) -∗
  instr_body 0x153b4 (accessListsTailEntry sp index old11 P).
Proof. zesu_block. Qed.
Print Assumptions access_lists_tail_guarded_correct.
