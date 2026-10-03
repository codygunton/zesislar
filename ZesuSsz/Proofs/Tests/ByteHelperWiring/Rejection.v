Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Section rejection.
Context `{!islaG Sigma} `{!threadG}.

Lemma reject_missing_scratch_owner : emp -∗ 65536 ↦ₘ? 48.
Proof. iIntros "Hempty". Fail solve [zesu_run]. Abort.

Lemma reject_wrong_scratch_address (bytes : list (bv 8))
    (Hlength : length bytes = 8%nat) :
  65536 ↦ₘ∗ bytes -∗ 65544 ↦ₘ? 40 -∗ 65600 ↦ₘ? 48.
Proof. iIntros "Hbytes Htail". Fail solve [zesu_run]. Abort.

Lemma reject_missing_payload_owner (tail : spec) (event : seq_event) :
  spec_trace (scons event tail) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    65536 ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗ spec_trace (scons event x.1ₗ).
Proof. iIntros "Htrace". Fail solve [zesu_run]. Abort.

Lemma reject_wrong_payload_address (bytes : list (bv 8)) (tail : spec) (event : seq_event) (Hlength : length bytes = 8%nat) :
  65536 ↦ₘ∗ bytes -∗ spec_trace (scons event tail) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    65600 ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗ spec_trace (scons event x.1ₗ).
Proof. iIntros "Hbytes Htrace". Fail solve [zesu_run]. Abort.

Lemma reject_wrong_first_event (bytes : list (bv 8)) (tail : spec) (Hlength : length bytes = 8%nat) :
  65536 ↦ₘ∗ bytes -∗ spec_trace (scons (SWriteMem (BV 64 604086464) (BV 64 1)) tail) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    65536 ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗
    spec_trace (scons (SWriteMem (BV 64 604086464) (BV 64 2)) x.1ₗ).
Proof. iIntros "Hbytes Htrace". Fail solve [zesu_run]. Abort.

Lemma reject_wrong_second_event (bytes : list (bv 8)) (tail : spec) (first : seq_event) (Hlength : length bytes = 8%nat) :
  65536 ↦ₘ∗ bytes -∗ spec_trace (scons first (scons (SWriteMem (BV 64 604086472) (BV 64 1)) tail)) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    65536 ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗
    spec_trace (scons first (scons (SWriteMem (BV 64 604086472) (BV 64 2)) x.1ₗ)).
Proof. iIntros "Hbytes Htrace". Fail solve [zesu_run]. Abort.

Lemma reject_wrong_event_address (bytes : list (bv 8)) (tail : spec)
    (Hlength : length bytes = 8%nat) :
  65536 ↦ₘ∗ bytes -∗ spec_trace (scons (SWriteMem (BV 64 604086464) (BV 64 1)) tail) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    65536 ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗
    spec_trace (scons (SWriteMem (BV 64 604086472) (BV 64 1)) x.1ₗ).
Proof. iIntros "Hbytes Htrace". Fail solve [zesu_run]. Abort.

Lemma reject_false_snapshot (bytes : list (bv 8)) (tail : spec) (event : seq_event) (Hlength : length bytes = 8%nat) :
  65536 ↦ₘ∗ bytes -∗ spec_trace (scons_snap event (fun _ => False%type) tail) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    65536 ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗
    spec_trace (scons_snap event (fun _ => True%type) x.1ₗ).
Proof. iIntros "Hbytes Htrace". Fail solve [zesu_run]. Abort.
End rejection.
