Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesByte.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesWord1Spec.
From IslaTraces.write_success_104 Require Import instrs.
From IslaTraces.write_success_105 Require Import instrs.
Local Remove Hints IslaTraces.write_success_105.a15864_spec.a15864_spec_inst : typeclass_instances.

Lemma suffix_word1_pack_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 10 (drop 22 IslaTraces.write_success_104.instrs.instr_map ++ take 21 IslaTraces.write_success_105.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15868 (suffixWord1Post sp pointer base source index P) -∗
  instr_body 0x15834 (suffixWord1Mid sp pointer base source index P).
Proof.
  zesu_block_simpl.
  all: unfold suffixWordByte; rewrite zesu_assemble_8_bytes
    (zesu_take_8_drop source (index + 8)%nat ltac:(lia)).
  all: repeat rewrite <- Nat.add_assoc; reflexivity.
Qed.
Print Assumptions suffix_word1_pack_correct.
