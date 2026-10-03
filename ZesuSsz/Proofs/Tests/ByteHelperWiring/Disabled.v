Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Local Remove Hints ZesuSsz.Automation.Switches.ArrayLoadPriority.zesu_switch_array_load_priority : typeclass_instances.
Local Remove Hints ZesuSsz.Automation.Switches.TracePrefixTail.zesu_switch_trace_prefix_tail : typeclass_instances.

Lemma reject_disabled_word_lookup (sp : bv 64)
    (w0 w1 w2 w3 w4 w5 w6 loaded : bv 64)
    (Hbound : bv_unsigned sp + 984 < 2 ^ 64)
    (Hlookup : [w0; w1; w2; w3; w4; w5; w6] !!
      Z.to_nat ((bv_unsigned (sp + BV 64 984) - (bv_unsigned sp + 936)) `div` 8) = Some loaded) :
  loaded = w6.
Proof. Fail solve [zesu_run]. Abort.

Definition disabled_folded_payload `{!islaG Sigma} (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (address ↦ₘ∗ bytes ∗ ⌜length bytes = 8%nat⌝)%I.

Lemma reject_disabled_payload `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list (bv 8)) (event : seq_event) (tail : spec)
    (Hlength : length bytes = 8%nat) :
  disabled_folded_payload address bytes -∗ spec_trace (scons event tail) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    address ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗ spec_trace (scons event x.1ₗ).
Proof. iIntros "Hbytes Htrace". Fail solve [zesu_run]. Abort.
