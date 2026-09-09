Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetNested.

Lemma writeSuccessConcreteRepresentationHeaderOkForget ok decoded memory address tailOk tail :
  (tailOk -> tail) ->
  writeSuccessConcreteRepresentationHeaderOk ok decoded memory address tailOk ->
  writeSuccessConcreteRepresentationHeaderPreR9 decoded memory address tail.
Proof.
  intros Htail H.
  unfold writeSuccessConcreteRepresentationHeaderOk,
    writeSuccessConcreteRepresentationHeaderPreR9 in *.
  destruct H as (Hvalid & Htop & Hnumber & Hlimit & Hused & Htime & Hextra & Hfee & Hrest).
  split; first exact Hvalid.
  split.
  - destruct Htop as (top & Hlength & Hread & _). exists top. auto.
  - split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hnumber).
    split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hlimit).
    split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hused).
    split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Htime).
    split; first exact (writeSuccessMemorySliceOkForget _ _ _ _ _ Hextra).
    split; first exact (writeSuccessMemoryIntegerOkForget _ _ _ _ _ Hfee).
    exact (Htail Hrest).
Qed.

Print Assumptions writeSuccessConcreteRepresentationHeaderOkForget.
