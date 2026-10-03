Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Import isla.riscv64.riscv64.
Open Scope Z_scope.

Lemma production_initialized_scratch `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (owner : bv 64)
    (Hlength : length bytes = 8%nat) :
  base ↦ₘ∗ bytes -∗ (base + 8) ↦ₘ? 40 -∗ "x19" ↦ᵣ RVal_Bits owner -∗
  base ↦ₘ? 48 ∗ "x19" ↦ᵣ RVal_Bits owner.
Proof. zesu_block. Qed.
Print Assumptions production_initialized_scratch.
