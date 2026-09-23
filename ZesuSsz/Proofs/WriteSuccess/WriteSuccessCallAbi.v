Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma zesu_c_call_ret_16_to_32 `{!islaG Sigma} `{!threadG}
    (regs : list valu) (ret sp : bv 64) (Q : list (bv 64) -> iProp Sigma) :
  instr_pre (bv_unsigned ret) (zesu_c_call_ret 32 regs ret sp Q) -∗
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret 16 regs ret sp (fun args =>
      (bv_unsigned sp - 32) ↦ₘ? 16 ∗ Q args)).
Proof. move => *. zesu_block. Qed.

Lemma zesu_c_call_ret_frame `{!islaG Sigma} `{!threadG}
    (stack_size : Z) (regs : list valu) (ret sp : bv 64)
    (F : iProp Sigma) (Q : list (bv 64) -> iProp Sigma) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stack_size regs ret sp (fun args => F ∗ Q args)) -∗
  F -∗
  instr_pre (bv_unsigned ret) (zesu_c_call_ret stack_size regs ret sp Q).
Proof. move => *. zesu_block. Qed.
