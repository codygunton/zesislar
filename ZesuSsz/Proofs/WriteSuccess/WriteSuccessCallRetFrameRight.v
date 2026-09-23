Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.

Lemma write_success_call_ret_frame_right
    `{!islaG Sigma} `{!threadG}
    (stackSize : Z) (regs : list valu) (ret sp : bv 64)
    (Q : list (bv 64) -> iProp Sigma) (F : iProp Sigma) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp (fun args => Q args ∗ F ∗ True)) -∗
  F -∗
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp (fun args => Q args ∗ True)).
Proof. move => *. zesu_block. Qed.

Lemma write_success_call_ret_frame_right2
    `{!islaG Sigma} `{!threadG}
    (stackSize : Z) (regs : list valu) (ret sp : bv 64)
    (Q1 Q2 : list (bv 64) -> iProp Sigma) (F : iProp Sigma) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp
      (fun args => Q1 args ∗ Q2 args ∗ F ∗ True)) -∗
  F -∗
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp
      (fun args => Q1 args ∗ Q2 args ∗ True)).
Proof. move => *. zesu_block. Qed.
