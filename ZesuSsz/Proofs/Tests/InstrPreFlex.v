Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.InstrPre.
Require Import isla.riscv64.riscv64.

Definition instrPreFlexQ `{!islaG Sigma} `{!threadG}
    (sp : bv 64) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ True)%I.
Global Instance : LithiumUnfold (@instrPreFlexQ) := I.

Lemma instr_pre_flex_body_to_pre `{!islaG Sigma} `{!threadG}
    (address : Z) (sp : bv 64) :
  ⊢ subsume (instr_body address ("x2" ↦ᵣ RVal_Bits sp ∗ True))
    (fun _ : unit => instr_pre address ("x2" ↦ᵣ RVal_Bits sp ∗ True))
    (fun _ => True%I).
Proof. zesu_block. Qed.

Lemma instr_pre_flex_framed_continuation `{!islaG Sigma} `{!threadG}
    (address : Z) (value : bv 64) (P : iProp Sigma) :
  P ∗ instr_pre address ("x10" ↦ᵣ RVal_Bits value ∗ P ∗ True) -∗
  instr_pre address ("x10" ↦ᵣ RVal_Bits value ∗ True).
Proof. zesu_block. Qed.

Lemma instr_pre_flex_identity_inference `{!islaG Sigma} `{!threadG}
    (address : Z) (sp : bv 64) :
  "x10" ↦ᵣ RVal_Bits sp ∗ instr_body address (instrPreFlexQ sp) -∗
  ∃ value : bv 64,
    "x10" ↦ᵣ RVal_Bits value ∗
    instr_pre address (instrPreFlexQ value) ∗ True.
Proof. zesu_block. Qed.

Lemma instr_pre_flex_legacy_guarded `{!islaG Sigma} `{!threadG}
    (address : Z) (sp ret : bv 64) :
  ⊢ subsume (instr_body address ("x2" ↦ᵣ RVal_Bits sp ∗ True))
    (fun _ : unit => instr_pre address
       ("x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits ret ∗ True))
    (fun _ => True%I).
Proof. zesu_block. Qed.

Print Assumptions instr_pre_flex_body_to_pre.
Print Assumptions instr_pre_flex_framed_continuation.
Print Assumptions instr_pre_flex_identity_inference.
Print Assumptions instr_pre_flex_legacy_guarded.
