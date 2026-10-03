Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.BoundedArithmetic.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments tactics.
Section tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma literal_covered_offset (root : bv 64) (bytes other : list (bv 8))
    (otherBase : Z) (P : iProp Sigma)
    (Hlength : length bytes = 848%nat)
    (Hend : (bv_unsigned root + 848 < 1073741824)%Z) :
  bv_unsigned (root + 0 + 0) ↦ₘ∗ bytes ∗ otherBase ↦ₘ∗ other ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (root + 0 + 720)))
      (fun _ => otherBase ↦ₘ∗ other ∗ P).
Proof using All.
  iIntros "[Hbytes [Hother HP]]".
  time zesu_preselect_covering_byte_array. iFrame.
Qed.
Lemma literal_zero_offset (root : bv 64) (bytes : list (bv 8))
    (P : iProp Sigma) (Hlength : length bytes = 848%nat)
    (Hend : (bv_unsigned root + 848 < 1073741824)%Z) :
  bv_unsigned root ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (root + 0))) (fun _ => P).
Proof using All. iIntros "[Hbytes HP]". zesu_preselect_covering_byte_array. iFrame. Qed.
Lemma literal_near_end_selection (root : bv 64) (bytes : list (bv 8))
    (P : iProp Sigma) (Hlength : length bytes = 848%nat)
    (Hend : (bv_unsigned root + 848 < 1073741824)%Z) :
  bv_unsigned root ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (root + 847))) (fun _ => P).
Proof using All. iIntros "[Hbytes HP]". zesu_preselect_covering_byte_array. iFrame. Qed.
Lemma literal_outside_rejects (root : bv 64) (bytes : list (bv 8))
    (P : iProp Sigma) (Hlength : length bytes = 848%nat)
    (Hend : (bv_unsigned root + 848 < 1073741824)%Z) :
  bv_unsigned root ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (root + 848))) (fun _ => P) ∨
    (P ∗ bv_unsigned root ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; zesu_preselect_covering_byte_array).
  iRight. iFrame.
Qed.
Lemma literal_missing_bound_rejects (root : bv 64) (bytes : list (bv 8))
    (P : iProp Sigma) (Hlength : length bytes = 848%nat) :
  bv_unsigned root ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (root + 720))) (fun _ => P) ∨
    (P ∗ bv_unsigned root ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; zesu_preselect_covering_byte_array).
  iRight. iFrame.
Qed.
Lemma literal_unresolved_pointer_rejects (root : bv 64) (bytes : list (bv 8))
    (P : iProp Sigma) (Hlength : length bytes = 848%nat)
    (Hend : (bv_unsigned root + 848 < 1073741824)%Z) :
  bv_unsigned root ↦ₘ∗ bytes ∗ P ⊢
    (∃ pointer : bv 64, find_in_context (FindMemMapsTo (bv_unsigned (pointer + 720))) (fun _ => P)) ∨
    (P ∗ bv_unsigned root ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; iExists _; zesu_preselect_covering_byte_array).
  iRight. iFrame.
Qed.
Lemma literal_near_end_load_rejects (root : bv 64) (bytes : list (bv 8))
    (P : iProp Sigma) (Hlength : length bytes = 848%nat)
    (Hend : (bv_unsigned root + 848 < 1073741824)%Z) :
  bv_unsigned root ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (root + 847)))
      (fun kind => match kind with
       | MKArray _ _ selected => ⌜(847 + 8 <= length selected)%nat⌝ ∗ P
       | _ => False end) ∨ (P ∗ bv_unsigned root ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; zesu_preselect_covering_byte_array;
    iSplit; [iPureIntro; lia | iFrame]).
  iRight. iFrame.
Qed.
End tests.
Section disabled.
Local Remove Hints zesu_switch_array_load_priority : typeclass_instances.
Lemma literal_disabled_rejects `{!islaG Sigma} `{!threadG}
    (root : bv 64) (bytes : list (bv 8)) (P : iProp Sigma)
    (Hlength : length bytes = 848%nat)
    (Hend : (bv_unsigned root + 848 < 1073741824)%Z) :
  bv_unsigned root ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (root + 720))) (fun _ => P) ∨
    (P ∗ bv_unsigned root ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; zesu_preselect_covering_byte_array).
  iRight. iFrame.
Qed.
End disabled.
Print Assumptions literal_covered_offset.
Print Assumptions literal_zero_offset.
Print Assumptions literal_near_end_selection.
Print Assumptions literal_outside_rejects.
Print Assumptions literal_missing_bound_rejects.
Print Assumptions literal_unresolved_pointer_rejects.
Print Assumptions literal_near_end_load_rejects.
Print Assumptions literal_disabled_rejects.
