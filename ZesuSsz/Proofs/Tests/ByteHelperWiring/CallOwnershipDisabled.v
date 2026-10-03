Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Local Remove Hints ZesuSsz.Automation.Switches.CallOwnership.zesu_switch_call_ownership : typeclass_instances.

Lemma reject_disabled_ownership_index (base : Z) :
  ZesuSsz.Contracts.IslarisMemory.array_region_start 64 (base + 936) (base + 984) = 6%nat.
Proof. Fail solve [zesu_run]. Abort.

Definition disabled_ownership_frame (entry : bv 64) : bv 64 := (entry - BV 64 2000)%bv.

Lemma reject_disabled_ownership_frame (entry : bv 64)
    (Hlower : 2176 <= bv_unsigned entry) :
  bv_unsigned (entry - BV 64 2048) = bv_unsigned (disabled_ownership_frame entry) - 48.
Proof. Fail solve [zesu_run]. Abort.

Lemma reject_disabled_ownership_empty_array `{!islaG Sigma} `{!threadG}
    (base address : Z) (word : bv 64) (Hrange : 0 <= address <= 2 ^ 64) :
  base ↦ₘ∗ [word] -∗ address ↦ₘ∗ ([] : list (bv 64)) ∗ base ↦ₘ∗ [word].
Proof. Fail solve [zesu_block]. Abort.

Definition disabled_ownership_payload `{!islaG Sigma} (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (address ↦ₘ∗ bytes ∗ ⌜length bytes = 8%nat⌝)%I.

Lemma reject_disabled_ownership_payload `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list (bv 8)) (event : seq_event) (tail : spec) :
  disabled_ownership_payload address bytes -∗ spec_trace (scons event tail) -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    address ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗ spec_trace (scons event x.1ₗ).
Proof. iIntros "Hbytes Htrace". Fail solve [zesu_run]. Abort.

(* The existing byte-array rule must keep its legacy result. *)
Lemma legacy_initialized_scratch `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (owner : bv 64)
    (Hlength : length bytes = 8%nat) :
  base ↦ₘ∗ bytes -∗ (base + 8) ↦ₘ? 40 -∗ "x19" ↦ᵣ RVal_Bits owner -∗
  base ↦ₘ? 48 ∗ "x19" ↦ᵣ RVal_Bits owner.
Proof. zesu_block. Qed.
Print Assumptions legacy_initialized_scratch.
