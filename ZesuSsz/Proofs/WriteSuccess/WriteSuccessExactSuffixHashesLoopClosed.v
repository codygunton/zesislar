Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesLoopSpec WriteSuccessExactSuffixHashesOutput
  WriteSuccessExactSuffixHashesLoopBody.

Lemma suffix_loop_closed `{!islaG Sigma} `{!threadG}
    sp base total source tail (P : iProp Sigma) :
  suffixWordsCode -∗
  ([∗ list] instruction ∈ drop 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_107.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15754 (suffixLoopSpec sp base total source tail P).
Proof.
  iStartProof. iIntros "#Hwords #Hemit #Htail #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (suffix_loop_body with "Hwords Hemit Htail Houtput IH").
Qed.
Print Assumptions suffix_loop_closed.
