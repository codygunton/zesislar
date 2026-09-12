Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma encoder_u256_exact_suffix_correct `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 10 IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15cd8 (encoderU256ExactSuffixSpec w0 w1 w2 w3 sp ret tail P).
Proof.
  zesu_block.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "u256 suffix residual" G end.
Qed.

Print Assumptions encoder_u256_exact_suffix_correct.
