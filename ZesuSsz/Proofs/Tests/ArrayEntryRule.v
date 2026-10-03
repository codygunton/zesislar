Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Automation.Switches.BoundedArithmetic.
Require Import ZesuSsz.Automation.Switches.WitnessArith.
From iris.proofmode Require Import environments tactics.
Open Scope Z_scope.

Definition preservedArrayFrameRaw `{!islaG Sigma} (value : bv 64) : iProp Sigma :=
  (10000 ↦ₘ value ∗ True)%I.
Definition preservedArrayFrame `{!islaG Sigma} (value : bv 64) : iProp Sigma := preservedArrayFrameRaw value.
Global Instance : LithiumUnfold (@preservedArrayFrame) := I.
Global Opaque preservedArrayFrame.
Definition arrayEntry `{!islaG Sigma} `{!threadG} (sp : bv 64) (values : list (bv 64)) : iProp Sigma :=
  (∃ saved : bv 64, "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 69 values ∗
   ⌜length values = 74%nat⌝ ∗ preservedArrayFrame saved)%I.
Global Instance : LithiumUnfold (@arrayEntry) := I.

Lemma test_array_entry_frame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) :
  arrayEntry sp values -∗
  ∃ saved : bv 64, "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 69 values ∗ preservedArrayFrame saved ∗ True.
Proof.
  iIntros "Hentry".
  zesu_prepare_array_entry_resources "x2".
  repeat iDestruct select (⌜_⌝)%I as %?.
  zesu_array_load_range (bv_unsigned sp + 1032)%Z (bv_unsigned sp + 1120)%Z 8 (take 69 values) 8.
  zesu_array_load_range (bv_unsigned sp + 1032)%Z (bv_unsigned sp + 1136)%Z 8 (take 69 values) 8.
  all: iMatchHyp ltac:(fun H frame =>
    lazymatch frame with preservedArrayFrame ?saved => iExists saved end).
  all: iRename select (preservedArrayFrame _) into "Hpreserved".
  all: iFrame.
Qed.
Print Assumptions test_array_entry_frame.
