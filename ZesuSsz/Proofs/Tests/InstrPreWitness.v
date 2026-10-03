Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Local Instance : ZesuStepCallOwnership := I.

Lemma instr_pre_witness_owned `{!islaG Sigma} `{!threadG}
    (address : Z) (resources : iProp Sigma) :
  instr_pre address resources -∗
  subsume (instr address None)
    (λ _ : unit, instr_pre address resources) (λ _ : unit, True).
Proof.
  iIntros "Hpre". zesu_close_owned_instr_pre_subsume.
Qed.
Print Assumptions instr_pre_witness_owned.

Lemma instr_pre_witness_missing `{!islaG Sigma} `{!threadG}
    (resources : iProp Sigma) :
  True -∗
  subsume (instr 0 None)
    (λ _ : unit, instr_pre 0 resources) (λ _ : unit, True) ∨ True.
Proof.
  iIntros "_".
  assert_fails (iLeft; zesu_close_owned_instr_pre_subsume).
  iRight. done.
Qed.

Lemma instr_pre_witness_wrong_address `{!islaG Sigma} `{!threadG}
    (resources : iProp Sigma) :
  instr_pre 1 resources -∗
  subsume (instr 0 None)
    (λ _ : unit, instr_pre 0 resources) (λ _ : unit, True) ∨ True.
Proof.
  iIntros "Hpre".
  assert_fails (iLeft; zesu_close_owned_instr_pre_subsume).
  iRight. done.
Qed.

Lemma instr_pre_witness_wrong_payload `{!islaG Sigma} `{!threadG} :
  instr_pre 4 (0 ↦ₘ (BV 8 1)) -∗
  subsume (instr 4 None)
    (λ _ : unit, instr_pre 4 (0 ↦ₘ (BV 8 2))) (λ _ : unit, True) ∨ True.
Proof.
  iIntros "Hpre".
  assert_fails (iLeft; zesu_close_owned_instr_pre_subsume).
  iRight. done.
Qed.

Lemma instr_pre_constant_resource `{!islaG Sigma} `{!threadG} :
  instr_pre 4 ("x1" ↦ᵣ RVal_Bits (BV 64 12)) -∗
  ∃ value : bv 64 *ₗ unit,
    instr_pre 4 ("x1" ↦ᵣ RVal_Bits (Z_to_bv 64 8 + 4)%bv) ∗
    ⌜value.1ₗ = BV 64 12⌝.
Proof.
  iIntros "Hpre". zesu_normalize_instr_pre_constants.
  iExists (BV 64 12, tt)ₗ. iFrame. done.
Qed.
Print Assumptions instr_pre_constant_resource.

Lemma instr_pre_constant_wrong_value `{!islaG Sigma} `{!threadG} :
  instr_pre 4 ("x1" ↦ᵣ RVal_Bits (BV 64 13)) -∗
  instr_pre 4 ("x1" ↦ᵣ RVal_Bits (Z_to_bv 64 8 + 4)%bv) ∨ True.
Proof.
  iIntros "Hpre". zesu_normalize_instr_pre_constants.
  assert_fails (iLeft; iExact "Hpre"). iRight. done.
Qed.
