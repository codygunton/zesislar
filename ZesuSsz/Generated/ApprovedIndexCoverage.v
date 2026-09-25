Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
From stdpp Require Import gmap.
Require Import isla.opsem.
Require Import ZesuSsz.Generated.ApprovedProgram.
Require Import IslaTraces.write_success_blocks.Index.

Definition approvedIndexCovered : bool :=
  List.forallb
    (fun address =>
      match IslaTraces.write_success_blocks.Index.lookup address with
      | Some _ => true
      | None => false
      end)
    approvedIndexAddresses.

Lemma approved_index_covered : approvedIndexCovered = true.
Proof. vm_compute. reflexivity. Qed.

Lemma approved_index_lookup address :
  List.In address approvedIndexAddresses ->
  exists trace,
    IslaTraces.write_success_blocks.Index.lookup address = Some trace.
Proof.
  intro Hin.
  pose proof approved_index_covered as Hcovered.
  unfold approvedIndexCovered in Hcovered.
  apply List.forallb_forall with (x := address) in Hcovered; last exact Hin.
  destruct (IslaTraces.write_success_blocks.Index.lookup address)
    as [trace|] eqn:Hlookup; simpl in Hcovered; try discriminate.
  exists trace. reflexivity.
Qed.

Print Assumptions approved_index_lookup.

Lemma approved_index_code_resolves address :
  List.In address approvedIndexAddresses ->
  exists trace, approvedProgram !! Z_to_bv 64 address = Some trace.
Proof.
  intros Hin.
  destruct (approved_index_lookup address Hin) as [trace Hlookup].
  apply (approved_index_address_resolves address trace); last exact Hlookup.
  apply elem_of_list_In. exact Hin.
Qed.

Print Assumptions approved_index_code_resolves.
