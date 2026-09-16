Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesLoopSpec WriteSuccessExactSuffixHashesLoopEntry
  WriteSuccessExactSuffixHashesOutput WriteSuccessExactSuffixHashesEmit
  WriteSuccessExactSuffixHashesEmitHandoff WriteSuccessExactSuffixHashesReturn
  WriteSuccessExactSuffixHashesTailLoop WriteSuccessExactSuffixHashesModel.

Lemma suffix_loop_body `{!islaG Sigma} `{!threadG}
    sp base total source tail (P : iProp Sigma) :
  suffixWordsCode -∗
  ([∗ list] instruction ∈ drop 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_107.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15754 (suffixLoopSpec sp base total source tail P) -∗
  instr_body 0x15754 (suffixLoopSpec sp base total source tail P).
Proof.
  iStartProof. iIntros "#Hwords #Hemit #Htail #Houtput #IH".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iEval (unfold suffixLoopSpec) in "Hentry".
  iDestruct "Hentry" as (processed remaining pointer old_ra old5) "Hentry".
  iPoseProof (suffix_loop_to_words sp pointer old_ra old5 base total processed remaining source tail P
    with "Hentry") as "HwordsEntry".
  iPoseProof (suffix_tail_loop_correct sp pointer base total processed remaining source tail P
    with "Htail IH") as "Hlast".
  iPoseProof (instr_pre_wand 0x158d4 0x158d4 false false with "Hlast []") as "Hnext".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (suffix_emit_to_tail with "Hpost"). }
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1744)%bv (BV 64 32)
    (BV 64 0x158d4) (take 32 (drop (32 * processed) source))
    (writeSuccessExactSuffixHashesEvents sp (S processed) remaining source tail)
    (suffixEmitFrame sp (suffixEmitCallerFrame sp pointer base source (32 * processed)
      (suffixLoopCaller sp pointer base total processed remaining source tail P)))))%I as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (write_output_trace_correct with "Houtput"). }
  iPoseProof (suffix_words_output_correct sp pointer base source (32 * processed) old_ra old5
    (writeSuccessExactSuffixHashesEvents sp (S processed) remaining source tail)
    (suffixLoopCaller sp pointer base total processed remaining source tail P)
    with "Hwords Hemit Hcallee Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody". iApply ("Hbody" with "HwordsEntry").
Qed.
Print Assumptions suffix_loop_body.
