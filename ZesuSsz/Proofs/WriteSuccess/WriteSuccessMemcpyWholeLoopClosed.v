Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessMemcpyWholeLoopBody.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_02 Require Import instrs.

Lemma memcpy_whole_loop_closed `{!islaG Sigma} `{!threadG}
    base start source src dst n ret (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d8 (memcpyWholeLoopSpec base start source src dst n ret P).
Proof.
  iIntros "#Hcode". iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (memcpy_whole_loop_body with "Hcode IH").
Qed.
Print Assumptions memcpy_whole_loop_closed.
