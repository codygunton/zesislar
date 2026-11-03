Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import isla.automation.
Require Import ZesuSsz.Automation.SourceRegisterOrigin194.
Require Import ZesuSsz.Automation.SourceRegisterCapture209.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
From Coq Require Import Strings.String.
Local Open Scope string_scope.

Lemma source_field_actual196 `{!islaG Sigma} `{!threadG}
    (register field : string) (word : bv 64) ann :
  register # field ↦ᵣ RegVal_Base (Val_Bits word) ⊢
  WPaexp (AExp_Val (AVal_Var register [Field field]) ann)
    {{ value, ⌜value = Val_Bits word⌝ ∗
       register # field ↦ᵣ RegVal_Base (Val_Bits word) }}.
Proof.
  iIntros "Hfield".
  iApply (zesu_wpaexp_source_register "field.actual" 64).
  iApply wpae_var_reg.
  iApply (read_reg_struct with "Hfield").
  iIntros "Hfield".
  zesu_capture_source_register_post203.
  SourceWitnessInputs.zesu_read_source_value constr:(bv 64) constr:("field.actual")
    ltac:(fun actual => constr_eq actual word).
  iSplit; [iPureIntro; reflexivity | iFrame].
Qed.

Lemma source_field_wrong_width196 `{!islaG Sigma} `{!threadG} (word : bv 32) :
  ⊢ zesu_source_register_post "field.width" 64
       (fun _ => True%I) (Val_Bits word).
Proof.
  iStartProof.
  Fail zesu_capture_source_register_post203.
  unfold zesu_source_register_post.
  destruct (bvn_to_bv 64 (bv_to_bvn word)) as [actual|] eqn:Hdecoded.
  all: try iIntros "_"; done.
Qed.

Lemma source_field_symbolic_width196 `{!islaG Sigma} `{!threadG}
    (width : N) (word : bv 64) :
  ⊢ zesu_source_register_post "field.symbolic" width
       (fun _ => True%I) (Val_Bits word).
Proof.
  iStartProof.
  Fail zesu_capture_source_register_post203.
  unfold zesu_source_register_post.
  destruct (bvn_to_bv width (bv_to_bvn word)) as [actual|] eqn:Hdecoded.
  all: try iIntros "_"; done.
Qed.
Print Assumptions source_field_actual196.
Print Assumptions source_field_wrong_width196.
Print Assumptions source_field_symbolic_width196.
