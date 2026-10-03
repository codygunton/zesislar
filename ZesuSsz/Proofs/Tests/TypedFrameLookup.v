Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Automation.StackArrayLookup.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.BoundedArithmetic.
Require Import ZesuSsz.Automation.Switches.WitnessArith.

Lemma typed_frame_lookup `{!islaG Sigma} (sp : bv 64) (values : list (bv 64)) :
  length values = 74%nat ->
  FindHypEqual (FICMemMapstoSemantic (bv_unsigned sp + 1120))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values)
    (mem_mapsto_kind_prop (bv_unsigned sp + 1032)
      (MKArray 64 (bv_unsigned sp + 1032) (take 69 values)))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values).
Proof.
  intros Hlength.
  timeout 5 typeclasses eauto.
Qed.
Print Assumptions typed_frame_lookup.

Lemma typed_frame_lookup13 `{!islaG Sigma} (sp : bv 64) (values : list (bv 64)) :
  length values = 74%nat ->
  FindHypEqual (FICMemMapstoSemantic (bv_unsigned sp + 1136))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values)
    (mem_mapsto_kind_prop (bv_unsigned sp + 1032)
      (MKArray 64 (bv_unsigned sp + 1032) (take 69 values)))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values).
Proof.
  intros Hlength.
  timeout 5 typeclasses eauto.
Qed.

Lemma typed_frame_lookup_raw `{!islaG Sigma} (sp : bv 64) (values : list (bv 64)) :
  length values = 74%nat ->
  (bv_unsigned sp + 1764 < machineRamEnd defaultMap)%Z ->
  FindHypEqual (FICMemMapstoSemantic (bv_unsigned (sp + 1120)))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values)
    (mem_mapsto_kind_prop (bv_unsigned sp + 1032)
      (MKArray 64 (bv_unsigned sp + 1032) (take 69 values)))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values).
Proof.
  intros Hlength Hram.
  timeout 5 typeclasses eauto.
Qed.

Print Assumptions typed_frame_lookup13.
Print Assumptions typed_frame_lookup_raw.

Lemma typed_frame_lookup_raw13 `{!islaG Sigma} (sp : bv 64) (values : list (bv 64)) :
  length values = 74%nat ->
  (bv_unsigned sp + 1764 < machineRamEnd defaultMap)%Z ->
  FindHypEqual (FICMemMapstoSemantic (bv_unsigned (sp + 1136)))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values)
    (mem_mapsto_kind_prop (bv_unsigned sp + 1032)
      (MKArray 64 (bv_unsigned sp + 1032) (take 69 values)))
    ((bv_unsigned sp + 1032) ↦ₘ∗ take 69 values).
Proof.
  intros Hlength Hram.
  timeout 5 typeclasses eauto.
Qed.


Print Assumptions typed_frame_lookup_raw13.

Definition preservedTypedFrameRaw `{!islaG Sigma} (word : bv 64) : iProp Sigma :=
  ((-16) ↦ₘ word)%I.
Definition preservedTypedFrame `{!islaG Sigma} (word : bv 64) : iProp Sigma :=
  preservedTypedFrameRaw word.
Global Instance : LithiumUnfold (@preservedTypedFrame) := I.
Global Opaque preservedTypedFrame.

Lemma typed_frame_search `{!islaG Sigma} (sp word : bv 64) (values : list (bv 64)) :
  length values = 74%nat ->
  (bv_unsigned sp + 1764 < machineRamEnd defaultMap)%Z ->
  (bv_unsigned sp + 1032) ↦ₘ∗ take 69 values ∗ preservedTypedFrame word -∗
  find_in_context (FindMemMapsTo (bv_unsigned (sp + 1136)))
    (fun _ => preservedTypedFrame word)%I.
Proof.
  intros Hlength Hram. iIntros "[Harray Hframe]".
  timeout 5 (repeat progress zesu_liAStep).
  iExact "Hframe".
Qed.
Print Assumptions typed_frame_search.
