Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesByte.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesWord3Spec.
From IslaTraces.write_success_103 Require Import instrs.
Local Remove Hints IslaTraces.write_success_103.a157ac_spec.a157ac_spec_inst : typeclass_instances.

Lemma suffix_word3_pack_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 10 (take 23 IslaTraces.write_success_103.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x157b0 (suffixWord3Post sp pointer base source index P) -∗
  instr_body 0x1577c (suffixWord3Mid sp pointer base source index P).
Proof.
  zesu_block.
  all: unfold suffixWordByte; rewrite zesu_assemble_8_bytes
    (zesu_take_8_drop source (index + 24)%nat ltac:(lia)).
  all: repeat rewrite <- Nat.add_assoc; reflexivity.
Qed.
Print Assumptions suffix_word3_pack_correct.
