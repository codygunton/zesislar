Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.main Require Import instrs.
Require Import ZesuSsz.Proofs.Main.Resources.

Definition mainDispatchInstrs : list (Z * isla_trace) :=
  [(0x14cfc, a14cfc); (0x14d00, a14d00)].

Lemma main_dispatch_success_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) :
  ([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x14d04
    (mainCallRegisters sp ra (BV 64 0) a1 ∗
     mainDispatchMemory sp (BV 16 0) ∗ True) -∗
  instr_body 0x14cfc
    (mainCallRegisters sp ra a0 a1 ∗
     mainDispatchMemory sp (BV 16 0) ∗ True).
Proof. unfold mainDispatchInstrs. zesu_block. all: exfalso; apply H6; apply bv_eq; vm_compute; reflexivity. Qed.
Print Assumptions main_dispatch_success_correct.

Lemma main_dispatch_failure_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (status : bv 16) :
  ([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x14d1c
    (mainCallRegisters sp ra (bv_zero_extend 64 status) a1 ∗
     mainDispatchMemory sp status ∗ True) -∗
  instr_body 0x14cfc
    (⌜bv_unsigned status <> 0⌝ ∗
     mainCallRegisters sp ra a0 a1 ∗ mainDispatchMemory sp status ∗ True).
Proof. unfold mainDispatchInstrs. zesu_block. all: exfalso; apply H0; apply (f_equal bv_unsigned) in H7; rewrite bv_zero_extend_unsigned in H7; [exact H7|lia]. Qed.
Print Assumptions main_dispatch_failure_correct.

Lemma main_dispatch_success_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x14d04
    (mainCallRegisters sp ra (BV 64 0) a1 ∗
     mainDispatchMemory sp (BV 16 0) ∗ True ∗ P ∗ True) -∗
  instr_body 0x14cfc
    (mainCallRegisters sp ra a0 a1 ∗
     mainDispatchMemory sp (BV 16 0) ∗ True ∗ P ∗ True).
Proof. unfold mainDispatchInstrs. zesu_block. all: exfalso; apply H6; apply bv_eq; vm_compute; reflexivity. Qed.
Print Assumptions main_dispatch_success_correct_with_frame.

Lemma main_dispatch_failure_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (status : bv 16) (P : iProp Sigma) :
  ([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x14d1c
    (mainCallRegisters sp ra (bv_zero_extend 64 status) a1 ∗
     mainDispatchMemory sp status ∗ True ∗ P ∗ True) -∗
  instr_body 0x14cfc
    (⌜bv_unsigned status <> 0⌝ ∗
     mainCallRegisters sp ra a0 a1 ∗ mainDispatchMemory sp status ∗ True ∗ P ∗ True).
Proof. unfold mainDispatchInstrs. zesu_block. all: exfalso; apply H0; apply (f_equal bv_unsigned) in H7; rewrite bv_zero_extend_unsigned in H7; [exact H7|lia]. Qed.
Print Assumptions main_dispatch_failure_correct_with_frame.
