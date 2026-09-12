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
Proof.
  zesu_block.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "u256 prefix residual" G end.
Qed.

Print Assumptions encoder_u256_exact_prefix_correct.
