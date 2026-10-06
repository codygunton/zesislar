Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.PureFacts.

Lemma list_witness_disabled {A : Type} (values : list A) (count : nat)
    (Hlength : length values = S count) :
  exists head tail, values = head :: tail /\ length tail = count.
Proof.
  Fail zesu_list_cons_witness_if_enabled.
  exact (zesu_list_cons_witness values count Hlength).
Qed.

Lemma list_witness_registered_disabled {A : Type} (values : list A)
    (count : nat) (source : Prop) (Hsource : source)
    `{derived : ZesuDerivedFacts source (length values = S count)} :
  exists head tail, values = head :: tail /\ length tail = count.
Proof.
  Fail zesu_list_cons_witness_if_enabled.
  exact (zesu_list_cons_witness values count
    (zesu_derived_facts (ZesuDerivedFacts := derived) Hsource)).
Qed.

Require Import ZesuSsz.Automation.Switches.ListWitness.

Lemma list_witness_owned_length {A : Type} (values : list A) (count : nat)
    (Hlength : length values = S count) :
  exists head tail, values = head :: tail /\ length tail = count.
Proof. zesu_list_cons_witness_if_enabled. Qed.

Definition list_witness_owned_facts {A : Type} (values : list A) (count : nat) :=
  length values = S count /\ True.

Lemma list_witness_folded_length {A : Type} (values : list A) (count : nat)
    (Howned : list_witness_owned_facts values count) :
  exists head tail, values = head :: tail /\ length tail = count.
Proof. zesu_finish. Qed.

Lemma list_witness_missing_length {A : Type} (count : nat) : True.
Proof.
  Fail assert (Hbad : exists head tail, (@nil A) = head :: tail /\
    length tail = count) by zesu_list_cons_witness_if_enabled.
  exact I.
Qed.

Lemma list_witness_unrelated_goal : True.
Proof. Fail zesu_list_cons_witness_if_enabled. exact I. Qed.

Print Assumptions list_witness_owned_length.
Print Assumptions list_witness_folded_length.

Lemma list_witness_registered_length {A : Type} (values : list A)
    (count : nat) (source : Prop) (Hsource : source)
    `{derived : ZesuDerivedFacts source (length values = S count)} :
  exists head tail, values = head :: tail /\ length tail = count.
Proof. zesu_list_cons_witness_if_enabled. Qed.

Lemma list_witness_registered_conjunction {A : Type} (values : list A)
    (count : nat) (source : Prop) (Hsource : source)
    `{derived : ZesuDerivedFacts source (length values = S count /\ True)} :
  exists head tail, values = head :: tail /\ length tail = count.
Proof. zesu_finish. Qed.

Print Assumptions list_witness_registered_disabled.
Print Assumptions list_witness_registered_length.
Print Assumptions list_witness_registered_conjunction.
