Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesByte.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesWord2Spec.
From IslaTraces.write_success_103 Require Import instrs.
From IslaTraces.write_success_104 Require Import instrs.
Local Remove Hints IslaTraces.write_success_104.a15808_spec.a15808_spec_inst : typeclass_instances.

Lemma suffix_word2_pack_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 10 (drop 23 IslaTraces.write_success_103.instrs.instr_map ++ take 22 IslaTraces.write_success_104.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1580c (suffixWord2Post sp pointer base source index P) -∗
  instr_body 0x157d8 (suffixWord2Mid sp pointer base source index P).
Proof.
  zesu_block_simpl.
  all: unfold suffixWordByte; rewrite zesu_assemble_8_bytes
    (zesu_take_8_drop source (index + 16)%nat ltac:(lia)).
  all: repeat rewrite <- Nat.add_assoc; reflexivity.
Qed.
Print Assumptions suffix_word2_pack_correct.
