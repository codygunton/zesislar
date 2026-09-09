Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetLeaves.
Require Import ZesuSsz.Experiments.WriteSuccessRepresentationForgetNested.

Lemma writeSuccessConcreteRepresentationHashesOkForget ok decoded memory address tailOk tail :
  (tailOk -> tail) ->
  writeSuccessConcreteRepresentationHashesOk ok decoded memory address tailOk ->
  writeSuccessConcreteRepresentationHashesPreR9 decoded memory address tail.
Proof.
  intros Htail H.
  unfold writeSuccessConcreteRepresentationHashesOk,
    writeSuccessConcreteRepresentationHashesPreR9 in *.
  destruct H as (Hparent & Hfee & Hstate & Hreceipts & Hlogs & Hrandao & Hblock &
    Hversions & Hdeposits & Hrequests & Hconsolidations & HbuilderDeposits &
    HbuilderExits & Hbeacon & Hrest).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hparent).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hfee).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hstate).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hreceipts).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hlogs).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hrandao).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hblock).
  split; first (eapply writeSuccessMemoryFixedListOkForget; exact Hversions).
  split; first (eapply writeSuccessMemorySliceOkForget; exact Hdeposits).
  split; first (eapply writeSuccessMemorySliceOkForget; exact Hrequests).
  split; first (eapply writeSuccessMemorySliceOkForget; exact Hconsolidations).
  split; first (eapply writeSuccessMemorySliceOkForget; exact HbuilderDeposits).
  split; first (eapply writeSuccessMemorySliceOkForget; exact HbuilderExits).
  split; first (eapply writeSuccessMemoryBytesOkForget; exact Hbeacon).
  exact (Htail Hrest).
Qed.

Print Assumptions writeSuccessConcreteRepresentationHashesOkForget.
