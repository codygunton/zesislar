Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Record ResourceWitnessLocals : Type := {
  resourceWitnessRegister : bv 64;
  resourceWitnessBytes : list (bv 8)
}.

Lemma record_witness_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepRecordWitness) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.RecordWitness.

Lemma record_witness_structural_goal : True.
Proof.
  Fail zesu_record_witness_if_enabled.
  exact I.
Qed.

Lemma record_witness_sum_guard : True.
Proof.
  Fail let _ := zesu_record_constructor_witness bool in idtac.
  exact I.
Qed.

Lemma record_witness_named_context (recordConstructorProbe : True) : True.
Proof.
  Fail let _ := zesu_record_constructor_witness bool in idtac.
  exact I.
Qed.

Lemma record_witness_proof_field_guard : True.
Proof.
  Fail let _ := zesu_record_constructor_witness (bv 64) in idtac.
  exact I.
Qed.

Lemma record_witness_unknown_type_guard : True.
Proof.
  Fail let unknown := open_constr:(_ : Type) in
    let _ := zesu_record_constructor_witness unknown in idtac.
  exact I.
Qed.

Lemma record_witness_resources `{!islaG Sigma} `{!threadG}
    (value : bv 64) (bytes : list (bv 8)) (address : Z) :
  "x10" ↦ᵣ RVal_Bits value -∗ address ↦ₘ∗ bytes -∗
  ∃ locals : li_prod ResourceWitnessLocals unit,
    "x10" ↦ᵣ RVal_Bits (resourceWitnessRegister locals.1ₗ) ∗
    address ↦ₘ∗ resourceWitnessBytes locals.1ₗ ∗ True.
Proof.
  iStartProof.
  zesu_run.
Qed.
Print Assumptions record_witness_resources.
