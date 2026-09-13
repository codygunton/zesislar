Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Lemma test_framed_wand `{!islaG Sigma} `{!threadG}
    (value : bv 64) (P : iProp Sigma) :
  P -∗ (("x10" ↦ᵣ RVal_Bits value ∗ True -∗
    "x10" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True).
Proof.
  iStartProof. iIntros "HP". zesu_finish_framed_wand.
Qed.

Lemma test_framed_continuation `{!islaG Sigma} `{!threadG}
    (address : Z) (value : bv 64) (P : iProp Sigma) :
  P ∗ instr_pre address ("x10" ↦ᵣ RVal_Bits value ∗ P ∗ True) -∗
  instr_pre address ("x10" ↦ᵣ RVal_Bits value ∗ True).
Proof. zesu_block. Qed.

Print Assumptions test_framed_wand.
Print Assumptions test_framed_continuation.
