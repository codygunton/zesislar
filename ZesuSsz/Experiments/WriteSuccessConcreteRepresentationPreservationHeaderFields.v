From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationPreservationCore.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.

Definition writeSuccessRepresentationHeaderFieldsOk
    (ok : Z -> nat -> Prop) decoded memory address (tail : Prop) : Prop :=
  writeSuccessMemoryIntegerOk ok memory address 8
    (observationBlockNumber decoded) /\
  writeSuccessMemoryIntegerOk ok memory (address + 8) 8
    (observationGasLimit decoded) /\
  writeSuccessMemoryIntegerOk ok memory (address + 16) 8
    (observationGasUsed decoded) /\
  writeSuccessMemoryIntegerOk ok memory (address + 24) 8
    (observationTimestamp decoded) /\
  writeSuccessMemorySliceOk ok memory address 32
    (observationExtraData decoded) /\
  writeSuccessMemoryIntegerOk ok memory (address + 48) 8
    (observationBaseFee decoded) /\ tail.

Lemma writeSuccessRepresentationHeaderFieldsOkReadsEqual
    ok decoded before after address beforeTail afterTail :
  writeSuccessRepresentationReadsEqual ok before after ->
  writeSuccessRepresentationHeaderFieldsOk ok decoded before address beforeTail ->
  afterTail ->
  writeSuccessRepresentationHeaderFieldsOk ok decoded after address afterTail.
Proof.
  intros Hreads (Hnumber & Hlimit & Hused & Htimestamp & Hextra & Hfee & _) Htail.
  repeat first
    [ solve [eapply writeSuccessMemoryIntegerOkReadsEqual; eassumption]
    | solve [eapply writeSuccessMemorySliceOkReadsEqual; eassumption]
    | split ].
  exact Htail.
Qed.

Print Assumptions writeSuccessRepresentationHeaderFieldsOkReadsEqual.
