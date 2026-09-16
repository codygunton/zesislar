Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Export
  WriteSuccessExactSuffixHashesWord1Spec
  WriteSuccessExactSuffixHashesWord1Load
  WriteSuccessExactSuffixHashesWord1Pack.

Lemma suffix_word1_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 22 IslaTraces.write_success_104.instrs.instr_map ++ take 21 IslaTraces.write_success_105.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15868 (suffixWord1Post sp pointer base source index P) -∗
  instr_body 0x1580c (suffixWord1Entry sp pointer base source index P).
Proof.
  iStartProof. iIntros "Hcode Hnext".
  iDestruct (big_sepL_take_drop _ _ 10 with "Hcode") as "[Hload Hpack]".
  iApply (suffix_word1_load_correct with "Hload").
  iApply (suffix_word1_pack_correct with "Hpack Hnext").
Qed.
Print Assumptions suffix_word1_correct.
