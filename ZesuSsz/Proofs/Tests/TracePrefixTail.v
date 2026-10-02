Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Sets.call.

Section tests.
Context `{!islaG Sigma} `{!threadG}.

Lemma test_snapshot_call_tail (event : seq_event)
    (accept : seq_snapshot -> Prop) (tail : spec) (address : Z) (P : iProp Sigma) :
  instr_pre address P -∗
  ∃ x : spec *ₗ (),
    ⌜scons_snap event accept x.1ₗ ⊆ scons_snap event accept tail⌝ ∗
    instr_pre address P.
Proof.
  iIntros "Hpre". zesu_close_matching_trace_tail. iExact "Hpre".
Qed.

Lemma test_event_snapshot_call_tail (first second : seq_event)
    (accept : seq_snapshot -> Prop) (tail : spec) (address : Z) (P : iProp Sigma) :
  instr_pre address P -∗
  ∃ x : spec *ₗ (),
    ⌜scons first (scons_snap second accept x.1ₗ) ⊆
      scons first (scons_snap second accept tail)⌝ ∗ instr_pre address P.
Proof.
  iIntros "Hpre". zesu_rule_set_v2_steps. iExact "Hpre".
Qed.

Lemma test_snapshot_predicate_guard (event : seq_event)
    (accept other : seq_snapshot -> Prop) (tail : spec) (address : Z) (P : iProp Sigma) :
  instr_pre address P -∗
  ∃ x : spec *ₗ (),
    ⌜scons_snap event accept x.1ₗ ⊆ scons_snap event accept tail⌝ ∗
    instr_pre address P.
Proof.
  iIntros "Hpre".
  Fail let candidate := constr:(tail) in
    let ignored := zesu_matching_trace_tail candidate
      (scons_snap event accept candidate) (scons_snap event other tail) in idtac.
  zesu_close_matching_trace_tail. iExact "Hpre".
Qed.
End tests.

Print Assumptions test_snapshot_call_tail.
Print Assumptions test_event_snapshot_call_tail.
Print Assumptions test_snapshot_predicate_guard.
