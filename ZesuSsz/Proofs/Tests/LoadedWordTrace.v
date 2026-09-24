Require Import ZesuSsz.Automation.Switches.LoadedWordTrace.
Require Import ZesuSsz.Automation.LoadedWordTrace.
Require Import isla.riscv64.riscv64.

Lemma loaded_word_trace_payload (words : list (bv 64)) (index : nat)
    (word fallback : bv 64) (tail : spec) :
  words !! index = Some word ->
  scons_snap (SWriteMem (BV 64 16) (BV 8 8))
    (fun _ : seq_snapshot => default fallback (words !! index) = word) tail ⊆
  scons_snap (SWriteMem (BV 64 16) (BV 8 8))
    (fun _ : seq_snapshot => word = word) tail.
Proof.
  intros Hlookup.
  zesu_rewrite_loaded_word_if_enabled.
  spec_solver.
Qed.

Print Assumptions loaded_word_trace_payload.

Lemma loaded_word_trace_two_payloads (words : list (bv 64))
    (first second : nat) (first_word second_word fallback : bv 64)
    (tail : spec) :
  words !! first = Some first_word ->
  words !! second = Some second_word ->
  scons_snap (SWriteMem (BV 64 16) (BV 8 8))
    (fun _ : seq_snapshot =>
      default fallback (words !! first) = first_word /\
      default fallback (words !! second) = second_word) tail ⊆
  scons_snap (SWriteMem (BV 64 16) (BV 8 8))
    (fun _ : seq_snapshot =>
      first_word = first_word /\ second_word = second_word) tail.
Proof.
  intros Hfirst Hsecond.
  zesu_rewrite_loaded_word_if_enabled.
  spec_solver.
Qed.

Print Assumptions loaded_word_trace_two_payloads.
