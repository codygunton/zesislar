Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOkTrue.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetHeader.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetLists.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetHashes.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetPostData.

Lemma writeSuccessConcreteRepresentationOffLegacy sp decoded memory address :
  writeSuccessConcreteRepresentationOff sp decoded memory address ->
  writeSuccessConcreteRepresentation decoded memory address.
Proof.
  intro H.
  apply (proj2 (writeSuccessConcreteRepresentationPreR9Iff _ _ _)).
  unfold writeSuccessConcreteRepresentationOff,
    writeSuccessConcreteRepresentationOk in H.
  unfold writeSuccessConcreteRepresentationPreR9.
  eapply writeSuccessConcreteRepresentationHeaderOkForget; [|exact H].
  intro Hlists.
  eapply writeSuccessConcreteRepresentationListsOkForget; [|exact Hlists].
  intro Hhashes.
  eapply writeSuccessConcreteRepresentationHashesOkForget; [|exact Hhashes].
  exact (writeSuccessConcreteRepresentationPostDataOkForget _ _ _ _).
Qed.

#[export] Hint Resolve writeSuccessConcreteRepresentationOffLegacy : core.
#[export] Hint Extern 1 (writeSuccessConcreteRepresentation _ _ _) =>
  eapply writeSuccessConcreteRepresentationOffLegacy; eassumption : core.

Print Assumptions writeSuccessConcreteRepresentationOffLegacy.
