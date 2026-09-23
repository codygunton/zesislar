Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Local Existing Instance subsume_instr_pre_guard_inst | 0.

Lemma encoder_u128_exact_output_correct `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 4
      IslaTraces.write_success_127.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 32)%bv
    (BV 64 16) (BV 64 0x15d04) (writeSuccessU128WordsPayload low high) tail
    (encoderU128ExactFrame low high sp ret tail P)) -∗
  instr_body 0x15d04 (encoderU128ExactSuffixSpec low high sp ret tail P) -∗
  instr_body 0x15cf4 (encoderU128ExactAtOutputSpec low high sp ret tail P).
Proof. move => *. zesu_block. Qed.

Print Assumptions encoder_u128_exact_output_correct.
