Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesByte.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesWord0Spec.
From IslaTraces.write_success_105 Require Import instrs.
From IslaTraces.write_success_106 Require Import instrs.
Local Remove Hints IslaTraces.write_success_106.a158c0_spec.a158c0_spec_inst : typeclass_instances.

Lemma suffix_word0_pack_correct `{!islaG Sigma} `{!threadG}
    sp pointer base source index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 10 (drop 21 IslaTraces.write_success_105.instrs.instr_map ++ take 20 IslaTraces.write_success_106.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x158c4 (suffixWord0Post sp pointer base source index P) -∗
  instr_body 0x15890 (suffixWord0Mid sp pointer base source index P).
Proof.
  zesu_block_simpl.
  all: zesu_unfold_bv_bindings.
  all: unfold suffixWordByte; rewrite zesu_assemble_8_bytes
    (zesu_take_8_drop source (index + 0)%nat ltac:(lia)).
  all: repeat rewrite <- Nat.add_assoc; zesu_finish_array_byte_lookup.
Qed.
Print Assumptions suffix_word0_pack_correct.
