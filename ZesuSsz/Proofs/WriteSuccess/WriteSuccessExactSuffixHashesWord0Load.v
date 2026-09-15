Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesByte.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesWord0Spec.
From IslaTraces.write_success_105 Require Import instrs.
From IslaTraces.write_success_106 Require Import instrs.
Local Remove Hints IslaTraces.write_success_106.a158c0_spec.a158c0_spec_inst : typeclass_instances.

Lemma suffix_word0_load_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 10 (drop 21 IslaTraces.write_success_105.instrs.instr_map ++ take 20 IslaTraces.write_success_106.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15890 (suffixWord0Mid sp pointer base source index P) -∗
  instr_body 0x15868 (suffixWord0Entry sp pointer base source index P).
Proof.
  unfold suffixWord0Mid, suffixWordByte. zesu_block_simpl.
Qed.
Print Assumptions suffix_word0_load_correct.
