Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.

Lemma test_existential_handoff `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P Q : iProp Sigma) :
  "x2" ↦ᵣ RVal_Bits sp -∗ P -∗ Q -∗
  ∃ x : bv 64 *ₗ unit,
    "x2" ↦ᵣ RVal_Bits x.1ₗ ∗ (P ∗ Q ∗ True) ∗ True.
Proof.
  iStartProof. iIntros "H2 HP HQ".
  zesu_handoff.
  Unshelve. all: try zesu_frame_handoff.
  Unshelve. all: try zesu_finish.
Qed.

Print Assumptions test_existential_handoff.
