From Coq Require Import Lists.List.
Require Import isla.opsem.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.

Lemma writeSuccessAndIff (P P' Q Q' : Prop) :
  (P <-> P') -> (Q <-> Q') -> (P /\ Q <-> P' /\ Q').
Proof.
  intros HP HQ. split.
  - intros [Hleft Hright]. split.
    + exact (proj1 HP Hleft).
    + exact (proj1 HQ Hright).
  - intros [Hleft Hright]. split.
    + exact (proj2 HP Hleft).
    + exact (proj2 HQ Hright).
Qed.

Lemma writeSuccessObjectBytesOkTrue memory address :
  (exists top,
      length top = 848%nat /\
      read_mem_list memory address 848%N = Some top /\ True) <->
  (exists top,
      length top = 848%nat /\
      read_mem_list memory address 848%N = Some top).
Proof.
  split.
  - intros (top & Hlength & Hread & _).
    exists top. tauto.
  - intros (top & Hlength & Hread).
    exists top. tauto.
Qed.

Print Assumptions writeSuccessAndIff.
Print Assumptions writeSuccessObjectBytesOkTrue.
