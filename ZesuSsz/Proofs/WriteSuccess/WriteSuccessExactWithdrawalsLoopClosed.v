Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsLoopBody.

Lemma withdrawal_loop_closed `{!islaG Sigma} `{!threadG}
    sp base rows source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_90.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_91.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_92.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_93.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_94.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_95.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15694 (withdrawalLoopSpec sp base rows source tail P).
Proof.
  iStartProof. iIntros "#H90 #H91 #H92 #H93 #H94 #H95 #Hcopy #Hint #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (withdrawal_loop_body with "H90 H91 H92 H93 H94 H95 Hcopy Hint Houtput IH").
Qed.
Print Assumptions withdrawal_loop_closed.

