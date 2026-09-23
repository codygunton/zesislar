Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.

Lemma encoder_u256_exact_prefix_correct `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 6 IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15cc8 (encoderU256ExactAtOutputWordsSpec w0 w1 w2 w3 sp ret tail P) -∗
  instr_body 0x15cb0 (encoderU256ExactSpec w0 w1 w2 w3 sp ret tail P).
Proof. move => *. zesu_block. Qed.

Print Assumptions encoder_u256_exact_prefix_correct.
