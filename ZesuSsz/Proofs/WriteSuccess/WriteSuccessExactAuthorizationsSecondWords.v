Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAuthorizationsWords.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_80 Require Import instrs.
Local Remove Hints IslaTraces.write_success_80.a155e4_spec.a155e4_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_80.a155e8_spec.a155e8_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_80.a155ec_spec.a155ec_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_80.a155f0_spec.a155f0_spec_inst : typeclass_instances.

Lemma authorization_second_words_correct `{!islaG Sigma} `{!threadG} sp bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_80.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x155f4 (authorizationWordsAtPost sp bytes 32 P) -∗
  instr_body 0x155e4 (authorizationWordsEntry sp bytes P).
Proof. move => *. zesu_block. Qed.
Print Assumptions authorization_second_words_correct.
