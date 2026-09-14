Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.main Require Import instrs.
Require Import ZesuSsz.Proofs.Main.Resources.

Definition main_write_success_instrs : list (Z * isla_trace) :=
  [(0x14d04, a14d04); (0x14d08, a14d08); (0x14d0c, a14d0c)].

Lemma main_write_success_call_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) :
  ([∗ list] i ∈ main_write_success_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x14d30
    (mainCallRegisters sp (BV 64 0x14d10) (sp + BV 64 32)%bv a1) -∗
  instr_body 0x14d04 (mainCallRegisters sp ra a0 a1).
Proof. unfold main_write_success_instrs. zesu_block. Qed.
Print Assumptions main_write_success_call_correct.

Definition main_write_failure_instrs : list (Z * isla_trace) :=
  [(0x14d1c, a14d1c); (0x14d20, a14d20)].

Lemma main_write_failure_call_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) :
  ([∗ list] i ∈ main_write_failure_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x161c0
    (mainCallRegisters sp (BV 64 0x14d24) a0 a1) -∗
  instr_body 0x14d1c (mainCallRegisters sp ra a0 a1).
Proof. unfold main_write_failure_instrs. zesu_block. Qed.
Print Assumptions main_write_failure_call_correct.

Definition main_success_exit_instrs : list (Z * isla_trace) :=
  [(0x14d10, a14d10); (0x14d14, a14d14); (0x14d18, a14d18)].

Lemma main_success_exit_call_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) :
  ([∗ list] i ∈ main_success_exit_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x101c4
    (mainCallRegisters sp (BV 64 0x14d1c) (BV 64 0) a1) -∗
  instr_body 0x14d10 (mainCallRegisters sp ra a0 a1).
Proof. unfold main_success_exit_instrs. zesu_block. Qed.
Print Assumptions main_success_exit_call_correct.

Definition main_failure_exit_instrs : list (Z * isla_trace) :=
  [(0x14d24, a14d24); (0x14d28, a14d28); (0x14d2c, a14d2c)].

Lemma main_failure_exit_call_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) :
  ([∗ list] i ∈ main_failure_exit_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x101c4
    (mainCallRegisters sp (BV 64 0x14d30) (BV 64 0) a1) -∗
  instr_body 0x14d24 (mainCallRegisters sp ra a0 a1).
Proof. unfold main_failure_exit_instrs. zesu_block. Qed.
Print Assumptions main_failure_exit_call_correct.


Lemma main_write_success_call_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ main_write_success_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x14d30
    (mainCallRegisters sp (BV 64 0x14d10) (sp + BV 64 32)%bv a1 ∗ P ∗ True) -∗
  instr_body 0x14d04 (mainCallRegisters sp ra a0 a1 ∗ P ∗ True).
Proof. unfold main_write_success_instrs. zesu_block. Qed.
Print Assumptions main_write_success_call_correct_with_frame.

Lemma main_write_failure_call_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ main_write_failure_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x161c0
    (mainCallRegisters sp (BV 64 0x14d24) a0 a1 ∗ P ∗ True) -∗
  instr_body 0x14d1c (mainCallRegisters sp ra a0 a1 ∗ P ∗ True).
Proof. unfold main_write_failure_instrs. zesu_block. Qed.
Print Assumptions main_write_failure_call_correct_with_frame.

Lemma main_success_exit_call_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ main_success_exit_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x101c4
    (mainCallRegisters sp (BV 64 0x14d1c) (BV 64 0) a1 ∗ P ∗ True) -∗
  instr_body 0x14d10 (mainCallRegisters sp ra a0 a1 ∗ P ∗ True).
Proof. unfold main_success_exit_instrs. zesu_block. Qed.
Print Assumptions main_success_exit_call_correct_with_frame.

Lemma main_failure_exit_call_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ main_failure_exit_instrs, instr i.1 (Some i.2)) -∗
  instr_body 0x101c4
    (mainCallRegisters sp (BV 64 0x14d30) (BV 64 0) a1 ∗ P ∗ True) -∗
  instr_body 0x14d24 (mainCallRegisters sp ra a0 a1 ∗ P ∗ True).
Proof. unfold main_failure_exit_instrs. zesu_block. Qed.
Print Assumptions main_failure_exit_call_correct_with_frame.
