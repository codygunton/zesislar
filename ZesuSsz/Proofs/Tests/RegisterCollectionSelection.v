Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

Lemma register_selection_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepRegisterCollectionSelection) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.RegisterCollectionSelection.

Lemma register_selection_array_first `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list byte) (shape : valu_shape)
    (T : reg_mapsto_kind -> iProp Sigma) :
  reg_col [(KindField "test_reg" "field", shape)] -∗
  address ↦ₘ∗ bytes -∗
  (address ↦ₘ∗ bytes -∗
    T (RKCol [(KindField "test_reg" "field", shape)])) -∗
  find_in_context (FindStructRegMapsTo "test_reg" "field") T.
Proof.
  iStartProof. iIntros "Hregs Harray HT".
  zesu_register_collection_selection_if_enabled.
  iApply "HT". iExact "Harray".
Qed.


Lemma register_selection_structural_goal : True.
Proof.
  Fail zesu_register_collection_selection_if_enabled.
  exact I.
Qed.

Lemma register_selection_skips_wrong_collection `{!islaG Sigma} `{!threadG}
    (shape other_shape : valu_shape) :
  reg_col [(KindField "test_reg" "field", shape)] -∗
  reg_col [(KindField "other_reg" "field", other_shape)] -∗
  find_in_context (FindStructRegMapsTo "test_reg" "field") (fun _ => True).
Proof.
  iStartProof. iIntros "Hregs Hother".
  zesu_register_collection_selection_if_enabled.
  done.
Qed.

Lemma register_selection_nonselection_alias `{!islaG Sigma} : True.
Proof.
  pose (Henv := @Envs (iPropI Sigma) Enil Enil 1%positive).
  Fail zesu_register_collection_selection_if_enabled.
  let value := eval unfold Henv in Henv in
  lazymatch value with Envs _ _ _ => idtac end.
  exact I.
Qed.
