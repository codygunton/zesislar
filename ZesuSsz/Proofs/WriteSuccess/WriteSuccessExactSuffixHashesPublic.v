Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesLoopSpec WriteSuccessExactSuffixHashesOutput
  WriteSuccessExactSuffixHashesLoopClosed WriteSuccessExactSuffixHashesInitial.

Lemma suffix_initial_closed `{!islaG Sigma} `{!threadG}
    sp base total source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_102.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  suffixWordsCode -∗
  ([∗ list] instruction ∈ drop 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_107.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15750 (suffixLoopSpec sp base total source tail P).
Proof.
  iStartProof. iIntros "#Hinitial #Hwords #Hemit #Htail #Houtput".
  iPoseProof (suffix_loop_closed sp base total source tail P with "Hwords Hemit Htail Houtput") as "#Hloop".
  iApply (suffix_initial_nonempty with "Hinitial Hloop").
Qed.
Print Assumptions suffix_initial_closed.
