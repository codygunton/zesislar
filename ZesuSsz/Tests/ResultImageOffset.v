From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ResultImage.

Lemma shifted_error_image_rejected (after : list byte) :
    (length after = 40)%nat ->
    valueImage after 1 40 (fun i => if Nat.eqb i 32 then 4 else 0) ->
    True.
Proof.
  intros Hlength Hshift.
  Fail exact (errorResult40_from_pointwise after Hlength Hshift).
  exact I.
Qed.
