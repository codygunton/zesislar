Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
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
Lemma test_snapshot_plain_call_tail (first second : seq_event)
    (accept : seq_snapshot -> Prop) (tail : spec) (address : Z) (P : iProp Sigma) :
  instr_pre address P -∗
  ∃ x : spec *ₗ (),
    ⌜scons first (scons_snap second accept x.1ₗ) ⊆
      scons first (scons second tail)⌝ ∗ instr_pre address P.
Proof.
  iIntros "Hpre". zesu_close_matching_trace_tail. iExact "Hpre".
Qed.
Lemma test_call_tail_keeps_next_event (first second next : seq_event)
    (accept : seq_snapshot -> Prop) (tail : spec) (address : Z) (P : iProp Sigma) :
  instr_pre address P -∗
  ∃ x : spec *ₗ (),
    ⌜scons first (scons_snap second accept x.1ₗ) ⊆
      scons first (scons_snap second accept (scons next tail))⌝ ∗
    instr_pre address P.
Proof.
  iIntros "Hpre".
  Fail zesu_open_trace_exist.
  zesu_close_matching_trace_tail. iExact "Hpre".
Qed.

End tests.

Print Assumptions test_snapshot_call_tail.
Print Assumptions test_event_snapshot_call_tail.
Print Assumptions test_snapshot_predicate_guard.
Print Assumptions test_snapshot_plain_call_tail.

Print Assumptions test_call_tail_keeps_next_event.

Lemma test_hidden_trace_continuation `{!islaG Sigma} `{!threadG}
    (event : seq_event) (accept : seq_snapshot -> Prop)
    (tail : spec) (pc : Z) (P : iProp Sigma) :
  instr_pre pc P -∗
  ∃ x : spec *ₗ (),
    ⌜scons_snap event accept x.1ₗ ⊆ scons_snap event accept tail⌝ ∗
    LET_ID (fun _ : spec *ₗ () => instr_pre pc P) x.
Proof.
  iIntros "Hnext".
  set (hidden := fun x : spec *ₗ () =>
    LET_ID (fun _ : spec *ₗ () => instr_pre pc P) x).
  lazymatch goal with |- envs_entails ?environment _ =>
    change (envs_entails environment (∃ x : spec *ₗ (),
      ⌜scons_snap event accept x.1ₗ ⊆ scons_snap event accept tail⌝ ∗ hidden x))
  end.
  zesu_close_matching_trace_tail.
  rewrite /hidden /LET_ID. iExact "Hnext".
Qed.
Print Assumptions test_hidden_trace_continuation.

Section tests.
Context `{!islaG Sigma}.
Context (events : bv 64 -> bv 64 -> list (bv 8) -> spec -> spec).
Lemma owned_trace_memory_witness (data size : bv 64) (bytes : list (bv 8)) (tail : spec) :
 spec_trace (events data size bytes tail) -∗ bv_unsigned data ↦ₘ∗ bytes -∗
 ∃ x : spec *ₗ list (bv 8) *ₗ (), bv_unsigned data ↦ₘ∗ x.2ₗ ∗ spec_trace (events data size x.2ₗ x.1ₗ).
Proof.
 iIntros "Htrace Hbytes".
 zesu_select_owned_trace_memory_witness.
 cbn. iFrame.
Qed.
Lemma owned_trace_preserves_unrelated (data other size : bv 64) (bytes unrelated : list (bv 8)) (tail otherTail : spec) :
 spec_trace (events data size bytes tail) -∗ bv_unsigned data ↦ₘ∗ bytes -∗
 spec_trace (events other size unrelated otherTail) -∗
 ∃ x : spec *ₗ list (bv 8) *ₗ (), bv_unsigned data ↦ₘ∗ x.2ₗ ∗
 spec_trace (events data size x.2ₗ x.1ₗ) ∗ spec_trace (events other size unrelated otherTail).
Proof.
 iIntros "Htrace Hbytes Hunrelated".
 zesu_select_owned_trace_memory_witness.
 cbn. iFrame.
Qed.
Lemma owned_trace_rejects_unrelated (data other size : bv 64) (bytes : list (bv 8)) (tail : spec) :
 spec_trace (events other size bytes tail) -∗ True.
Proof.
 iIntros "Htrace".
 Fail (iAssert (∃ x : spec *ₗ list (bv 8) *ₗ (), bv_unsigned data ↦ₘ∗ x.2ₗ ∗ spec_trace (events data size x.2ₗ x.1ₗ))%I with "[Htrace]" as "Himpossible";
   [zesu_select_owned_trace_memory_witness |]).
 done.
Qed.
Lemma owned_trace_computed_pointer (bytes : list (bv 8)) (tail : spec) :
 spec_trace (events (BV 64 96709) (BV 64 6) bytes tail) -∗
 bv_unsigned (BV 64 96709) ↦ₘ∗ bytes -∗
 ∃ x : spec *ₗ list (bv 8) *ₗ (),
 bv_unsigned (BV 64 85504 + BV 64 12288 + BV 64 18446744073709550533) ↦ₘ∗ x.2ₗ ∗
 spec_trace (events (BV 64 85504 + BV 64 12288 + BV 64 18446744073709550533) (BV 64 6) x.2ₗ x.1ₗ).
Proof.
 iIntros "Htrace Hbytes".
 zesu_select_owned_trace_memory_witness.
 cbn. iFrame.
Qed.
End tests.
Print Assumptions owned_trace_memory_witness.
Print Assumptions owned_trace_preserves_unrelated.

Print Assumptions owned_trace_rejects_unrelated.

Print Assumptions owned_trace_computed_pointer.

Section nested_owned_trace_tests.
Context `{!islaG Sigma}.
Context (events : bv 64 -> bv 64 -> list (bv 8) -> spec -> spec).
Lemma owned_trace_nested_memory (data size : bv 64) (bytes : list (bv 8)) (tail : spec) :
 spec_trace (events data size bytes tail) -∗ bv_unsigned data ↦ₘ∗ bytes -∗
 ∃ (x : list (bv 8) *ₗ ()) (next : spec), bv_unsigned data ↦ₘ∗ x.1ₗ ∗ spec_trace (events data size x.1ₗ next).
Proof.
 iIntros "Htrace Hbytes".
 zesu_select_owned_trace_memory_witness.
 cbn. iFrame.
Qed.
Lemma owned_trace_nested_preserves_unrelated (data other size : bv 64) (bytes unrelated : list (bv 8)) (tail otherTail : spec) :
 spec_trace (events data size bytes tail) -∗ bv_unsigned data ↦ₘ∗ bytes -∗
 spec_trace (events other size unrelated otherTail) -∗
 ∃ (x : list (bv 8) *ₗ ()) (next : spec), bv_unsigned data ↦ₘ∗ x.1ₗ ∗
 spec_trace (events data size x.1ₗ next) ∗ spec_trace (events other size unrelated otherTail).
Proof.
 iIntros "Htrace Hbytes Hunrelated".
 zesu_select_owned_trace_memory_witness.
 cbn. iFrame.
Qed.
Lemma owned_trace_nested_computed_pointer (bytes : list (bv 8)) (tail : spec) :
 spec_trace (events (BV 64 96709) (BV 64 6) bytes tail) -∗
 bv_unsigned (BV 64 96709) ↦ₘ∗ bytes -∗
 ∃ (x : list (bv 8) *ₗ ()) (next : spec),
 bv_unsigned (BV 64 85504 + BV 64 12288 + BV 64 18446744073709550533) ↦ₘ∗ x.1ₗ ∗
 spec_trace (events (BV 64 85504 + BV 64 12288 + BV 64 18446744073709550533) (BV 64 6) x.1ₗ next).
Proof.
 iIntros "Htrace Hbytes".
 zesu_select_owned_trace_memory_witness.
 cbn. iFrame.
Qed.
Lemma owned_trace_nested_rejects_unrelated (data other size : bv 64) (bytes : list (bv 8)) (tail : spec) :
 spec_trace (events other size bytes tail) -∗ True.
Proof.
 iIntros "Htrace".
 Fail (iAssert (∃ (x : list (bv 8) *ₗ ()) (next : spec), bv_unsigned data ↦ₘ∗ x.1ₗ ∗ spec_trace (events data size x.1ₗ next))%I with "[Htrace]" as "Himpossible";
   [zesu_select_owned_trace_memory_witness |]).
 done.
Qed.
End nested_owned_trace_tests.

Print Assumptions owned_trace_nested_memory.
Print Assumptions owned_trace_nested_preserves_unrelated.
Print Assumptions owned_trace_nested_computed_pointer.
Print Assumptions owned_trace_nested_rejects_unrelated.

Section owned_trace_array_guard_tests.
Context `{!islaG Sigma}.
Context (events : bv 64 -> bv 64 -> list (bv 8) -> spec -> spec).
Lemma owned_trace_rejects_larger_array (data size : bv 64)
    (larger : list (bv 8)) (tail : spec) (Hlength : length larger = 720%nat) :
 spec_trace (events data size (take 32 (drop 688 larger)) tail) -∗
 bv_unsigned data ↦ₘ∗ larger -∗
 bv_unsigned data ↦ₘ∗ larger ∗
 spec_trace (events data size (take 32 (drop 688 larger)) tail).
Proof.
 iIntros "Htrace Harray".
 Fail (iAssert (∃ x : spec *ₗ list (bv 8) *ₗ (),
   bv_unsigned data ↦ₘ∗ x.2ₗ ∗ spec_trace (events data size x.2ₗ x.1ₗ))%I
   with "[Htrace Harray]" as "Himpossible";
   [zesu_select_owned_trace_memory_witness |]).
 Fail (iAssert (∃ (x : list (bv 8) *ₗ ()) (next : spec),
   bv_unsigned data ↦ₘ∗ x.1ₗ ∗ spec_trace (events data size x.1ₗ next))%I
   with "[Htrace Harray]" as "Himpossible";
   [zesu_select_owned_trace_memory_witness |]).
 iFrame.
Qed.
End owned_trace_array_guard_tests.
Print Assumptions owned_trace_rejects_larger_array.

Require Import ZesuSsz.Export.Snapshots.
#[local] Instance : ZesuStepTracePrefixTail := I.
Lemma plain_nested_exact `{!islaG Sigma} (data size : bv 64) (bytes : list (bv 8)) (tail otherTail : spec) :
 bv_unsigned data ↦ₘ∗ bytes -∗ spec_trace otherTail -∗ spec_trace (writeOutputEvents data size bytes tail) -∗
 ∃ payload : list (bv 8), ∃ rest : spec, bv_unsigned data ↦ₘ∗ payload ∗ spec_trace (writeOutputEvents data size payload rest) ∗ spec_trace otherTail.
Proof. iIntros "Hbytes Hother Htrace". zesu_select_owned_trace_memory_witness. iFrame. Qed.
Lemma plain_nested_rejects_cover `{!islaG Sigma} (base : Z) (data size : bv 64) (large bytes : list (bv 8)) (tail : spec)
 (Hlength : length large = 720%nat)
 (Haddress : bv_unsigned data = base + 688)
 (Hpayload : bytes = take 32 (drop 688 large)) :
 base ↦ₘ∗ large -∗ spec_trace (writeOutputEvents data size bytes tail) -∗ True.
Proof. iIntros "Hlarge Htrace".
 Fail (iAssert (∃ payload : list (bv 8), ∃ rest : spec, bv_unsigned data ↦ₘ∗ payload ∗ spec_trace (writeOutputEvents data size payload rest))%I with "[Hlarge Htrace]" as "Hbad"; [zesu_select_owned_trace_memory_witness |]).
 done. Qed.
Lemma plain_nested_computed_preserves_other `{!islaG Sigma}
 (bytes other : list (bv 8)) (tail : spec) (base : Z) :
 bv_unsigned (BV 64 96709) ↦ₘ∗ bytes -∗ base ↦ₘ∗ other -∗
 spec_trace (writeOutputEvents (BV 64 96709) (BV 64 6) bytes tail) -∗
 ∃ payload : list (bv 8), ∃ rest : spec,
 bv_unsigned ((Z_to_bv 64 85504 + 12288 + 18446744073709550533)%bv) ↦ₘ∗ payload ∗
 spec_trace (writeOutputEvents ((Z_to_bv 64 85504 + 12288 + 18446744073709550533)%bv) (BV 64 6) payload rest) ∗ base ↦ₘ∗ other.
Proof. iIntros "Hbytes Hother Htrace". zesu_select_owned_trace_memory_witness. iFrame. Qed.
