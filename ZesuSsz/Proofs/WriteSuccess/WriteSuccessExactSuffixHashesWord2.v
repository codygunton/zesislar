Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Export
  WriteSuccessExactSuffixHashesWord2Spec
  WriteSuccessExactSuffixHashesWord2Load
  WriteSuccessExactSuffixHashesWord2Pack.

Lemma suffix_word2_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 23 IslaTraces.write_success_103.instrs.instr_map ++ take 22 IslaTraces.write_success_104.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1580c (suffixWord2Post sp pointer base source index P) -∗
  instr_body 0x157b0 (suffixWord2Entry sp pointer base source index P).
Proof.
  iStartProof. iIntros "Hcode Hnext".
  iDestruct (big_sepL_take_drop _ _ 10 with "Hcode") as "[Hload Hpack]".
  iApply (suffix_word2_load_correct with "Hload").
  iApply (suffix_word2_pack_correct with "Hpack Hnext").
Qed.
Print Assumptions suffix_word2_correct.
