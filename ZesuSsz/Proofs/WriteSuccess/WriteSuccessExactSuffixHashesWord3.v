Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Export
  WriteSuccessExactSuffixHashesWord3Spec
  WriteSuccessExactSuffixHashesWord3Load
  WriteSuccessExactSuffixHashesWord3Pack.

Lemma suffix_word3_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 23 IslaTraces.write_success_103.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x157b0 (suffixWord3Post sp pointer base source index P) -∗
  instr_body 0x15754 (suffixWord3Entry sp pointer base source index P).
Proof.
  iStartProof. iIntros "Hcode Hnext".
  iDestruct (big_sepL_take_drop _ _ 10 with "Hcode") as "[Hload Hpack]".
  iApply (suffix_word3_load_correct with "Hload").
  iApply (suffix_word3_pack_correct with "Hpack Hnext").
Qed.
Print Assumptions suffix_word3_correct.
