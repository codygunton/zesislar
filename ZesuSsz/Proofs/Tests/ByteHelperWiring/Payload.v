Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Definition production_payload `{!islaG Sigma} (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (address ↦ₘ∗ bytes ∗ ⌜length bytes = 8%nat⌝)%I.

Lemma production_folded_payload `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list (bv 8)) (first second : seq_event)
    (accept : seq_snapshot -> Prop) (tail : spec) (owner : bv 64) :
  production_payload address bytes -∗
  spec_trace (scons first (scons_snap second accept tail)) -∗
  "x19" ↦ᵣ RVal_Bits owner -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    address ↦ₘ∗ x.2ₗ ∗ ⌜length x.2ₗ = 8%nat⌝ ∗
    spec_trace (scons first (scons_snap second accept x.1ₗ)) ∗
    "x19" ↦ᵣ RVal_Bits owner.
Proof. zesu_block. Qed.
Print Assumptions production_folded_payload.
