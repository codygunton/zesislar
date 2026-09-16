Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesWord3 WriteSuccessExactSuffixHashesWord2
  WriteSuccessExactSuffixHashesWord1 WriteSuccessExactSuffixHashesWord0
  WriteSuccessExactSuffixHashesWordHandoffs.

Lemma suffix_words_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 23 IslaTraces.write_success_103.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ drop 23 IslaTraces.write_success_103.instrs.instr_map ++
    take 22 IslaTraces.write_success_104.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ drop 22 IslaTraces.write_success_104.instrs.instr_map ++
    take 21 IslaTraces.write_success_105.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ drop 21 IslaTraces.write_success_105.instrs.instr_map ++
    take 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x158c4 (suffixWord0Post sp pointer base source index
    (suffixWordFrame0 sp source index P)) -∗
  instr_body 0x15754 (suffixWord3Entry sp pointer base source index
    (suffixWordFrame3 sp source index P)).
Proof.
  iStartProof. iIntros "#H3 #H2 #H1 #H0 Hnext".
  iPoseProof (suffix_word0_correct sp pointer base source index
    (suffixWordFrame0 sp source index P) with "H0 Hnext") as "Hword0".
  iPoseProof (instr_pre_wand 0x15868 0x15868 false false with "Hword0 []") as "Hnext1".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (suffix_word1_handoff with "Hpost"). }
  iPoseProof (suffix_word1_correct sp pointer base source index
    (suffixWordFrame1 sp source index P) with "H1 Hnext1") as "Hword1".
  iPoseProof (instr_pre_wand 0x1580c 0x1580c false false with "Hword1 []") as "Hnext2".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (suffix_word2_handoff with "Hpost"). }
  iPoseProof (suffix_word2_correct sp pointer base source index
    (suffixWordFrame2 sp source index P) with "H2 Hnext2") as "Hword2".
  iPoseProof (instr_pre_wand 0x157b0 0x157b0 false false with "Hword2 []") as "Hnext3".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (suffix_word3_handoff with "Hpost"). }
  iApply (suffix_word3_correct sp pointer base source index
    (suffixWordFrame3 sp source index P) with "H3 Hnext3").
Qed.
Print Assumptions suffix_words_correct.
