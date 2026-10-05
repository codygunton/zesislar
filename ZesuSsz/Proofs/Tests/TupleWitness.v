Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.RecordWitness.

Lemma tuple_witness_disabled `{!islaG Sigma} `{!threadG}
    (value : bv 64) (bytes : list byte) (address : Z) :
  "x10" ↦ᵣ RVal_Bits value -∗ address ↦ₘ∗ bytes -∗
  ∃ locals : li_prod (bv 64) (li_prod (list byte) unit),
    "x10" ↦ᵣ RVal_Bits locals.1ₗ ∗ address ↦ₘ∗ locals.2ₗ ∗ True.
Proof.
  iIntros "Hregister Harray".
  Fail zesu_record_witness_if_enabled.
  Fail zesu_primitive_tuple_if_enabled.
  iExists (value, (bytes, tt)ₗ)ₗ. iFrame.
Qed.

Require Import ZesuSsz.Automation.Switches.TupleWitness.

Lemma tuple_witness_resources `{!islaG Sigma} `{!threadG}
    (value : bv 64) (bytes : list byte) (address : Z) :
  "x10" ↦ᵣ RVal_Bits value -∗ address ↦ₘ∗ bytes -∗
  ∃ locals : li_prod (bv 64) (li_prod (list byte) unit),
    "x10" ↦ᵣ RVal_Bits locals.1ₗ ∗ address ↦ₘ∗ locals.2ₗ ∗ True.
Proof. zesu_block. Qed.

Lemma tuple_witness_unrelated_goal : True.
Proof. Fail zesu_primitive_tuple_if_enabled. exact I. Qed.

Lemma tuple_witness_proof_field_guard : True.
Proof.
  Fail let _ := zesu_primitive_tuple_witness (li_prod True unit) in idtac.
  exact I.
Qed.

Lemma tuple_witness_unknown_type_guard : True.
Proof.
  Fail let T := open_constr:(_ : Type) in
    let _ := zesu_primitive_tuple_witness T in idtac.
  exact I.
Qed.

Lemma tuple_witness_missing_resource `{!islaG Sigma} `{!threadG} : True.
Proof.
  Fail assert (Hmissing : (⊢ ∃ locals : li_prod (bv 64) unit,
    "x10" ↦ᵣ RVal_Bits locals.1ₗ ∗ True)%I) by zesu_block.
  exact I.
Qed.

Print Assumptions tuple_witness_resources.
