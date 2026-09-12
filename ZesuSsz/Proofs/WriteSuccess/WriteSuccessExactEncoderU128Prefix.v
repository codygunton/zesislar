Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128.

Lemma encoder_u128_exact_prefix_correct `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15cf4 (encoderU128ExactAtOutputWordsSpec low high sp ret tail P) -∗
  instr_body 0x15ce4 (encoderU128ExactSpec low high sp ret tail P).
Proof.
  zesu_block.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "u128 prefix residual" G end.
Qed.

Print Assumptions encoder_u128_exact_prefix_correct.
