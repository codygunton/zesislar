Require Import ZesuSsz.Automation.All.
From lithium Require Import simpl_classes.
Require Import ZesuSsz.Automation.FactRegistry.

Definition registryPremise (P : Prop) : Prop := P.
Definition registryGoal (P : Prop) : Prop := P.
Definition registryPairGoal (P Q : Prop) : Prop := P /\ Q.
Definition registryHiddenPremise (key hidden : nat) : Prop := key = hidden.
Definition registryHiddenGoal (key : nat) : Prop := exists hidden, key = hidden.
#[local] Typeclasses Opaque registryPremise registryGoal registryPairGoal.
#[local] Typeclasses Opaque registryHiddenPremise registryHiddenGoal.

#[local] Instance registryAtomicInstance (P : Prop) (H : ZesuFactEvidence (registryPremise P)) :
  SimplAnd (registryGoal P) True | 1 := zesu_simpl_and_fact (@zesu_fact_evidence _ H).
#[local] Instance registryPairInstance (P Q : Prop)
    (Hleft : ZesuFactEvidence (registryPremise P))
    (Hright : ZesuFactEvidence (registryPremise Q)) :
  SimplAnd (registryPairGoal P Q) True | 1 :=
  zesu_simpl_and_fact (conj (@zesu_fact_evidence _ Hleft) (@zesu_fact_evidence _ Hright)).
#[local] Instance registryHiddenInstance (key hidden : nat)
    (H : ZesuFactEvidence (registryHiddenPremise key hidden)) :
  SimplAnd (registryHiddenGoal key) True | 1 :=
  zesu_simpl_and_fact (ex_intro (fun hidden => key = hidden) hidden (@zesu_fact_evidence _ H)).

Lemma registryConstructor (P : Prop) (H : P) : SimplAnd P True.
Proof. exact (zesu_simpl_and_fact H). Qed.
Lemma registryOrdinaryPremise (P : Prop) (H : registryPremise P) :
  SimplAnd (registryGoal P) True.
Proof. typeclasses eauto. Qed.
Lemma registryConjunctionPremises (P Q : Prop)
    (Hleft : registryPremise P) (Hright : registryPremise Q) :
  SimplAnd (registryPairGoal P Q) True.
Proof. typeclasses eauto. Qed.
Lemma registryHiddenParameter (key hidden : nat)
    (H : registryHiddenPremise key hidden) :
  SimplAnd (registryHiddenGoal key) True.
Proof. typeclasses eauto. Qed.
Lemma registryMissingPremiseRefusal (P : Prop) : True.
Proof.
  Fail assert (SimplAnd (registryGoal P) True) by typeclasses eauto.
  exact I.
Qed.
Lemma registryWrongPremiseRefusal (P Q : Prop) (H : registryPremise Q) : True.
Proof.
  Fail assert (SimplAnd (registryGoal P) True) by typeclasses eauto.
  exact I.
Qed.
Print Assumptions registryConstructor.
Print Assumptions registryOrdinaryPremise.
Print Assumptions registryConjunctionPremises.
Print Assumptions registryHiddenParameter.
Print Assumptions registryMissingPremiseRefusal.
Print Assumptions registryWrongPremiseRefusal.

Lemma registryTwoCandidates (P : Prop)
    (Hfirst Hsecond : registryPremise P) : True.
Proof.
  let selected := constr:(_ : ZesuFactEvidence (registryPremise P)) in
  idtac "RAW_EVIDENCE" selected;
  let reduced := eval cbv beta delta [zesu_fact_evidence_fast_done] in selected in
  idtac "REDUCED_EVIDENCE" reduced;
  lazymatch reduced with
  | @Build_ZesuFactEvidence _ Hsecond => exact I
  end.
Qed.
Print Assumptions registryTwoCandidates.

Lemma registryUnresolvedRefusal : True.
Proof.
  evar (pending : Prop).
  let hole := eval unfold pending in pending in
  is_evar hole;
  tryif assert (ZesuFactEvidence hole) by typeclasses eauto
  then fail "An unresolved proposition acquired evidence"
  else (is_evar hole; unify hole True).
  exact I.
Qed.
Print Assumptions registryUnresolvedRefusal.
