Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Lemma test_snapshot_write_preserves_payload
    `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 (writeOutputTraceSpec data size ret payload tail P).
Proof. apply write_output_trace_correct. Qed.

Print Assumptions test_snapshot_write_preserves_payload.
