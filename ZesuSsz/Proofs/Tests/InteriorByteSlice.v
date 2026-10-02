Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.InteriorByteSlice.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.

Definition testDeclaredByteArray `{!islaG Sigma} (base : Z)
    (bytes : list (bv 8)) : iProp Sigma := (base ↦ₘ∗ bytes ∗ True)%I.
Lemma testDeclaredByteArray_unfold `{!islaG Sigma} (base : Z)
    (bytes : list (bv 8)) :
  testDeclaredByteArray base bytes ⊣⊢ (base ↦ₘ∗ bytes ∗ True)%I.
Proof. done. Qed.
Global Opaque testDeclaredByteArray.
Global Instance testDeclaredByteArray_sealed `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) :
  ZesuSealed (testDeclaredByteArray base bytes) (base ↦ₘ∗ bytes ∗ True)%I
    [(base, base + Z.of_nat (length bytes))] [] :=
  testDeclaredByteArray_unfold base bytes.

Lemma test_sealed_interior_byte_slice `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (tail : spec) :
  length bytes = 592%nat ->
  testDeclaredByteArray base bytes -∗
  testDeclaredByteArray (base + 1000) bytes -∗ spec_trace tail -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    (base + 152)%Z ↦ₘ∗ x.2ₗ ∗ spec_trace x.1ₗ ∗
    ⌜32%Z = Z.of_nat (length x.2ₗ)⌝ ∗
    testDeclaredByteArray (base + 1000) bytes ∗
    ((base + 152)%Z ↦ₘ∗ x.2ₗ -∗ base ↦ₘ∗ bytes).
Proof.
  iIntros (Hlength) "Harray Hunrelated Htrace".
  zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro.
  rewrite length_take length_drop. lia.
Qed.
Print Assumptions test_sealed_interior_byte_slice.

Lemma test_interior_byte_slice `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (tail : spec) :
  length bytes = 592%nat ->
  base ↦ₘ∗ bytes -∗ spec_trace tail -∗
  ∃ x : spec *ₗ list (bv 8) *ₗ (),
    (base + 152)%Z ↦ₘ∗ x.2ₗ ∗ spec_trace x.1ₗ ∗
    ⌜32%Z = Z.of_nat (length x.2ₗ)⌝ ∗
    ((base + 152)%Z ↦ₘ∗ x.2ₗ -∗ base ↦ₘ∗ bytes).
Proof.
  iIntros (Hlength) "Harray Htrace".
  zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro.
  rewrite length_take length_drop. lia.
Qed.
Print Assumptions test_interior_byte_slice.

Lemma test_interior_byte_slice_return `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 592%nat ->
  base ↦ₘ∗ bytes -∗ base ↦ₘ∗ bytes ∗ True.
Proof.
  iIntros (Hlength) "Harray".
  iDestruct (zesu_byte_array_lend_slice base bytes 152 32
    with "Harray") as "[Hslice Hrestore]"; [lia|].
  zesu_restore_interior_byte_slice.
  iFrame.
Qed.
Print Assumptions test_interior_byte_slice_return.
