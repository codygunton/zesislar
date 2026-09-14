Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Export
  WriteSuccessExactSuffixHashesWord0Spec
  WriteSuccessExactSuffixHashesWord0Load
  WriteSuccessExactSuffixHashesWord0Pack.

Lemma suffix_word0_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 21 IslaTraces.write_success_105.instrs.instr_map ++ take 20 IslaTraces.write_success_106.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x158c4 (suffixWord0Post sp pointer base source index P) -∗
  instr_body 0x15868 (suffixWord0Entry sp pointer base source index P).
Proof.
  iStartProof. iIntros "Hcode Hnext".
  iDestruct (big_sepL_take_drop _ _ 10 with "Hcode") as "[Hload Hpack]".
  iApply (suffix_word0_load_correct with "Hload").
  iApply (suffix_word0_pack_correct with "Hpack Hnext").
Qed.
Print Assumptions suffix_word0_correct.
