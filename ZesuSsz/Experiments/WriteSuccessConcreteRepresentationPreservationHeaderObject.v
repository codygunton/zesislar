From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.

Definition writeSuccessRepresentationTopOk
    (ok : Z -> nat -> Prop) (memory : mem_map) (address : Z) : Prop :=
  exists top,
    length top = 848%nat /\
    read_mem_list memory address 848%N = Some top /\
    ok address (length top).

Lemma writeSuccessRepresentationTopOkReadsEqual ok before after address :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessRepresentationTopOk ok before address ->
  writeSuccessRepresentationTopOk ok after address.
Proof.
  intros Hreads (top & Hlength & Htop & Hok).
  exists top. split; first exact Hlength.
  split.
  - change (read_mem_list after address (N.of_nat 848%nat) = Some top).
    rewrite (Hreads address 848%nat).
    + exact Htop.
    + rewrite <- Hlength. exact Hok.
  - exact Hok.
Qed.

Print Assumptions writeSuccessRepresentationTopOkReadsEqual.
