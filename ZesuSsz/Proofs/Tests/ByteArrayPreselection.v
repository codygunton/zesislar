Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.BoundedArithmetic.
From iris.proofmode Require Import environments tactics.
Require Import isla.isla.
Section tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma covering_array_preserves (base : Z) (bytes : list (bv 8))
    (address : Z) (P : iProp Sigma)
    (Hcoverage : (base <= address < base + length bytes)%Z) :
  base ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo address)
      (fun _ => P).
Proof using All.
  iIntros "[Hbytes HP]".
  time zesu_array_load_priority.
  iFrame.
Qed.
Lemma noncovering_array_rejects (base address : Z) (bytes : list (bv 8))
    (P : iProp Sigma) :
  base ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo address) (fun _ => P) ∨
    (P ∗ base ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; zesu_array_load_priority).
  iRight. iFrame.
Qed.
Lemma symbolic_covering_array (base : Z) (bytes : list (bv 8))
    (pointer : bv 64) (processed remaining : nat) (P : iProp Sigma)
    (Hbase : (0 <= base)%Z)
    (Hend : (base + length bytes < 1073741824)%Z)
    (Hroot : (bv_unsigned pointer = base + 32 * Z.of_nat processed)%Z)
    (Hlength : length bytes = (32 * (processed + S remaining))%nat) :
  base ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo (bv_unsigned (pointer + 9))) (fun _ => P).
Proof using All.
  iIntros "[Hbytes HP]".
  time zesu_array_load_priority.
  iFrame.
Qed.

Lemma unresolved_address_rejects (base : Z) (bytes : list (bv 8))
    (P : iProp Sigma) :
  base ↦ₘ∗ bytes ∗ P ⊢
    (∃ address, find_in_context (FindMemMapsTo address) (fun _ => P)) ∨
    (P ∗ base ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; iExists _; zesu_array_load_priority).
  iRight. iFrame.
Qed.
End tests.
Print Assumptions covering_array_preserves.
Print Assumptions noncovering_array_rejects.

Print Assumptions symbolic_covering_array.

Section disabled.
Local Remove Hints zesu_switch_array_load_priority : typeclass_instances.
Lemma disabled_array_priority `{!islaG Sigma} `{!threadG}
    (base address : Z) (bytes : list (bv 8)) (P : iProp Sigma)
    (Hcoverage : (base <= address < base + length bytes)%Z) :
  base ↦ₘ∗ bytes ∗ P ⊢
    find_in_context (FindMemMapsTo address) (fun _ => P) ∨
    (P ∗ base ↦ₘ∗ bytes).
Proof using All.
  iIntros "[Hbytes HP]".
  assert_fails (iLeft; zesu_array_load_priority).
  iRight. iFrame.
Qed.
End disabled.
Print Assumptions disabled_array_priority.
