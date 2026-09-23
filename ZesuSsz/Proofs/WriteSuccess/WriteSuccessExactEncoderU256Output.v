Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Lemma encoder_u256_exact_output_correct `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 6
      IslaTraces.write_success_08.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 48)%bv
    (BV 64 32) (BV 64 0x15cd8) (writeSuccessU256WordsPayload w0 w1 w2 w3) tail
    (encoderU256ExactFrame w0 w1 w2 w3 sp ret tail P)) -∗
  instr_body 0x15cd8 (encoderU256ExactSuffixSpec w0 w1 w2 w3 sp ret tail P) -∗
  instr_body 0x15cc8 (encoderU256ExactAtOutputSpec w0 w1 w2 w3 sp ret tail P).
Proof. move => *. zesu_block. Qed.

Print Assumptions encoder_u256_exact_output_correct.
