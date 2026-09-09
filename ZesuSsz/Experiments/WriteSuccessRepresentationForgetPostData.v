Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetNested.

Lemma writeSuccessConcreteRepresentationPostDataOkForget ok decoded memory address :
  writeSuccessConcreteRepresentationPostDataOk ok decoded memory address ->
  writeSuccessConcreteRepresentationPostDataPreR9 decoded memory address.
Proof.
  intros H.
  unfold writeSuccessConcreteRepresentationPostDataOk,
    writeSuccessConcreteRepresentationPostDataPreR9 in *.
  destruct H as (Hnodes & Hcodes & Hheaders & Hchain & Hfork & Hindex &
    Hblock & Htime & Hkeys).
  split; first (eapply writeSuccessMemoryByteListsOkForget; exact Hnodes).
  split; first (eapply writeSuccessMemoryByteListsOkForget; exact Hcodes).
  split; first (eapply writeSuccessMemoryByteListsOkForget; exact Hheaders).
  split; first (eapply writeSuccessMemoryIntegerOkForget; exact Hchain).
  split; first (eapply writeSuccessMemoryOptionalBytesOkForget; exact Hfork).
  split; first (eapply writeSuccessMemoryIntegerOkForget; exact Hindex).
  split; first (eapply writeSuccessMemoryOptionalU64OkForget; exact Hblock).
  split; first (eapply writeSuccessMemoryOptionalU64OkForget; exact Htime).
  eapply writeSuccessMemoryByteListsOkForget. exact Hkeys.
Qed.

Print Assumptions writeSuccessConcreteRepresentationPostDataOkForget.
