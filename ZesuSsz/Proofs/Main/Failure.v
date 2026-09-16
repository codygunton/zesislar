Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.Main.FailureAdapter.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteFailure.TraceContract.

Lemma main_failure_trace_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] i ∈ mainFailurePrefixInstrs, instr i.1 (Some i.2)) -∗
  ([∗ list] i ∈ skipn 5 IslaTraces.write_failure.instrs.instr_map,
    instr i.1 (Some i.2)) -∗
  instr_body 0x161c0 (mainFailureTraceEntry tail P).
Proof. apply write_failure_framed_trace_correct. Qed.
Print Assumptions main_failure_trace_correct.

Lemma main_failure_canonical_trace_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] i ∈ mainFailurePrefixInstrs, instr i.1 (Some i.2)) -∗
  ([∗ list] i ∈ writeFailureCanonicalOutputInstrs,
    instr i.1 (Some i.2)) -∗
  instr_body 0x161c0 (mainFailureTraceEntry tail P).
Proof. apply write_failure_canonical_framed_trace_correct. Qed.
Print Assumptions main_failure_canonical_trace_correct.
