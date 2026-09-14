Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesWords WriteSuccessExactSuffixHashesWord3
  WriteSuccessExactSuffixHashesWordHandoffs WriteSuccessExactSuffixHashesEmit
  WriteSuccessExactSuffixHashesEmitHandoff.

Definition suffixWordsCode `{!islaG Sigma} : iProp Sigma :=
  ([∗ list] block ∈ [take 23 IslaTraces.write_success_103.instrs.instr_map;
    drop 23 IslaTraces.write_success_103.instrs.instr_map ++ take 22 IslaTraces.write_success_104.instrs.instr_map;
    drop 22 IslaTraces.write_success_104.instrs.instr_map ++ take 21 IslaTraces.write_success_105.instrs.instr_map;
    drop 21 IslaTraces.write_success_105.instrs.instr_map ++ take 20 IslaTraces.write_success_106.instrs.instr_map],
   [∗ list] instruction ∈ block, instr instruction.1 (Some instruction.2))%I.

Lemma suffix_words_output_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index old_ra old5 tail (P : iProp Sigma) :
  suffixWordsCode -∗
  ([∗ list] instruction ∈ drop 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1744)%bv (BV 64 32)
    (BV 64 0x158d4) (take 32 (drop index source)) tail
    (suffixEmitFrame sp (suffixEmitCallerFrame sp pointer base source index P))) -∗
  instr_body 0x158d4 (suffixEmitPost sp (take 32 (drop index source)) tail
    (suffixEmitCallerFrame sp pointer base source index P)) -∗
  instr_body 0x15754 (suffixWord3Entry sp pointer base source index
    (suffixWordFrame3 sp source index
      (suffixOutputResources sp old_ra old5 (take 32 (drop index source)) tail P))).
Proof.
  iStartProof. iIntros "#Hwords #Hemit #Houtput Hnext".
  iEval (rewrite /suffixWordsCode !big_sepL_cons big_sepL_nil) in "Hwords".
  iDestruct "Hwords" as "(H3 & H2 & H1 & H0 & _)".
  iAssert (instr_body 0x158c4 (∃ old_data old_size : bv 64,
    suffixEmitEntry sp old_ra old5 old_data old_size (take 32 (drop index source)) tail
      (suffixEmitCallerFrame sp pointer base source index P))) with "[Hnext]" as "Hcall".
  { iApply instr_body_exists. iIntros (old_data).
    iApply instr_body_exists. iIntros (old_size).
    iApply (suffix_emit_correct sp old_ra old5 old_data old_size (take 32 (drop index source)) tail
      (suffixEmitCallerFrame sp pointer base source index P) with "Hemit Houtput Hnext"). }
  iPoseProof (instr_pre_wand 0x158c4 0x158c4 false false with "Hcall []") as "Hnext".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (suffix_words_to_emit with "Hpost"). }
  iApply (suffix_words_correct sp pointer base source index
    (suffixOutputResources sp old_ra old5 (take 32 (drop index source)) tail P)
    with "H3 H2 H1 H0 Hnext").
Qed.
Print Assumptions suffix_words_output_correct.
