From Coq Require Import ZArith.ZArith.
Require Import isla.opsem.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessStackRange.

Definition writeSuccessConcreteRepresentationOff
    (sp : Z) (decoded : WriteSuccessObservation)
    (memory : mem_map) (address : Z) : Prop :=
  writeSuccessConcreteRepresentationOk
    (writeSuccessAvoidsRange (writeSuccessCalleeStackLow sp) sp)
    decoded memory address.

Lemma writeSuccessConcreteRepresentationOffObject
    sp decoded memory address :
  writeSuccessConcreteRepresentationOff sp decoded memory address ->
  writeSuccessAvoidsRange (writeSuccessCalleeStackLow sp) sp address 848%nat.
Proof.
  intros Hrepresentation.
  unfold writeSuccessConcreteRepresentationOff in Hrepresentation.
  pose proof (writeSuccessConcreteRepresentationOkObject
    _ _ _ _ Hrepresentation) as (top & Hlength & _ & Havoids).
  rewrite Hlength in Havoids. exact Havoids.
Qed.

Print Assumptions writeSuccessConcreteRepresentationOffObject.
