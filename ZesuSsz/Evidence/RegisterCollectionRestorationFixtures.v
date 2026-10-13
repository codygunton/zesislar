Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.RegisterCollectionSelection.

Lemma registerCollectionRestorationMasked `{!islaG Sigma} `{!threadG} :
  ⊢ ((∃ value : valu, ⌜valu_has_shape value (StructShape [("bits", MaskShape 64 131072 0)])⌝ ∗ "mstatus" ↦ᵣ value)%I -∗ find_in_context (FindStructRegMapsTo "mstatus" "bits")
  (λ kind, match kind with
  | RKCol registers => reg_col registers -∗ reg_col [(KindReg "mstatus", StructShape [("bits", MaskShape 64 131072 0)])]
  | _ => False
  end))%I.
Proof.
  iIntros "Hregister". zesu_register_collection_selection_if_enabled.
  iIntros "Hreturned". iExact "Hreturned".
Qed.

Lemma registerCollectionRestorationExact `{!islaG Sigma} `{!threadG} :
  ⊢ (("mtvec" ↦ᵣ RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))])%I -∗ find_in_context (FindStructRegMapsTo "mtvec" "bits")
  (λ kind, match kind with
  | RKCol registers => reg_col registers -∗ reg_col [(KindReg "mtvec", ExactShape (RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))]))]
  | _ => False
  end))%I.
Proof.
  iIntros "Hregister". zesu_register_collection_selection_if_enabled.
  iIntros "Hreturned". iExact "Hreturned".
Qed.

Lemma registerCollectionRestorationExisting `{!islaG Sigma} `{!threadG} :
  ⊢ ((reg_col [(KindReg "mstatus", StructShape [("bits", MaskShape 64 131072 0)])])%I -∗ find_in_context (FindStructRegMapsTo "mstatus" "bits")
  (λ kind, match kind with
  | RKCol registers => reg_col registers -∗ reg_col [(KindReg "mstatus", StructShape [("bits", MaskShape 64 131072 0)])]
  | _ => False
  end))%I.
Proof.
  iIntros "Hregister". zesu_register_collection_selection_if_enabled.
  iIntros "Hreturned". iExact "Hreturned".
Qed.

