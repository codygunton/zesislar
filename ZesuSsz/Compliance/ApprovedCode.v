Require Import ZesuSsz.Automation.All.
From stdpp Require Import gmap.
Require Import isla.opsem.
Require Import ZesuSsz.Generated.ApprovedProgram.
Require Import ZesuSsz.Generated.ApprovedIndexCoverage.
Require Import ZesuSsz.Compliance.Program.

Lemma approved_contract_code_resolves (P : AdmissibleProgram) address :
  address ∈ approvedContractCodeKeys ->
  exists trace, programInstructions P !! address = Some trace.
Proof.
  intros Hkey.
  destruct (approved_code_key_resolves address Hkey) as [trace Hlookup].
  exists trace. exact (approved_program_no_shadow P address trace Hlookup).
Qed.

Print Assumptions approved_contract_code_resolves.

Definition approvedContractNamedPc (address : Z) : Prop :=
  (exists trace, (address, trace) ∈ approvedContractSourceInstructions) \/
  address ∈ approvedIndexAddresses.

Lemma approved_contract_named_pc_resolves (P : AdmissibleProgram) address :
  approvedContractNamedPc address ->
  exists trace, programInstructions P !! Z_to_bv 64 address = Some trace.
Proof.
  intros [[source Hsource] | Hindex].
  - destruct (approved_source_code_resolves address source Hsource)
      as [trace Hlookup].
    exists trace. exact (approved_program_no_shadow P _ _ Hlookup).
  - apply elem_of_list_In in Hindex.
    destruct (approved_index_code_resolves address Hindex)
      as [trace Hlookup].
    exists trace. exact (approved_program_no_shadow P _ _ Hlookup).
Qed.

Print Assumptions approved_contract_named_pc_resolves.
