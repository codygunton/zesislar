Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import tactics environments.
Require Import ZesuSsz.Automation.All.

Inductive CompatibilityAbsent : Prop := CompatibilityAbsentHere.
Inductive CompatibilityValid : Prop := CompatibilityValidHere.
Inductive CompatibilityInvalid : Prop := CompatibilityInvalidHere.

#[local] Instance compatibility_valid_mapping (Sigma : gFunctors) :
    ZesuEntrySourceWitnessMapping (⌜CompatibilityValid⌝%I : iProp Sigma) unit unit := {
  zesu_source_witness_input := ZesuSourceUnit;
  zesu_source_witness_mapping := fun _ => tt
}.

#[local] Instance compatibility_invalid_mapping (Sigma : gFunctors) :
    ZesuEntrySourceWitnessMapping (⌜CompatibilityInvalid⌝%I : iProp Sigma) nat nat := {
  zesu_source_witness_input := ZesuSourceValue nat "compatibility-invalid"%string;
  zesu_source_witness_mapping := fun value => value
}.

Lemma source_optional_absent (Sigma : gFunctors) :
  ⊢ (⌜CompatibilityAbsent⌝%I : iProp Sigma).
Proof.
  iStartProof.
  first [SourceWitnessInputs.zesu_source_mapping_capture_goal;
    fail 1 "An absent optional mapping succeeded." | idtac].
  iPureIntro. constructor.
Qed.

Lemma source_optional_transient `{!islaG Sigma} `{!threadG} (pc : bv 64) :
  "PC" ↦ᵣ RVal_Bits pc -∗ "PC" ↦ᵣ RVal_Bits pc.
Proof.
  iIntros "Hpc".
  let unknown := open_constr:(_ : bv 64) in
  iAssert ("PC" ↦ᵣ RVal_Bits unknown)%I with "[Hpc]" as "Hpc".
  - Fail lazymatch goal with
      | |- environments.envs_entails _ ?requested =>
          SourceWitnessInputs.zesu_source_mapping_capture requested
      end.
    first [SourceWitnessInputs.zesu_source_mapping_capture_goal;
      fail 1 "An unresolved optional mapping succeeded." | idtac].
    iExact "Hpc".
  - iExact "Hpc".
Qed.

Lemma source_registered_invalid (Sigma : gFunctors) :
  ⊢ (⌜CompatibilityInvalid⌝%I : iProp Sigma).
Proof.
  iStartProof.
  let registration := constr:(_ : ZesuEntrySourceWitnessMapping
    (⌜CompatibilityInvalid⌝%I : iProp Sigma) nat nat) in idtac.
  let unknown := open_constr:(_ : nat) in
  pose proof (@ZesuSourceWitnessHere nat "compatibility-invalid"%string unknown)
    as Hinvalid.
  Fail SourceWitnessInputs.zesu_source_mapping_capture_goal.
  lazymatch goal with
  | Hinvalid : @ZesuSourceWitness nat _ ?value |- _ => unify value O
  end.
  iPureIntro. constructor.
Qed.

Lemma source_registered_missing (Sigma : gFunctors) :
  ⊢ (⌜CompatibilityInvalid⌝%I : iProp Sigma).
Proof.
  iStartProof.
  let registration := constr:(_ : ZesuEntrySourceWitnessMapping
    (⌜CompatibilityInvalid⌝%I : iProp Sigma) nat nat) in idtac.
  Fail first [SourceWitnessInputs.zesu_source_mapping_capture_goal |
    idtac "SOURCE_READER_FALLBACK_SENTINEL"].
  iPureIntro. constructor.
Qed.

Lemma source_registered_valid (Sigma : gFunctors) :
  ⊢ (⌜CompatibilityValid⌝%I : iProp Sigma).
Proof.
  iStartProof.
  SourceWitnessInputs.zesu_source_mapping_capture_goal.
  lazymatch goal with
  | _ : @ZesuEntryWitnessPending _ unit ?key ?data |- _ =>
      let expected := constr:(⌜CompatibilityValid⌝%I : iProp Sigma) in
      constr_eq key expected;
      let reduced := eval cbv in data in constr_eq reduced tt
  end.
  iPureIntro. constructor.
Qed.
