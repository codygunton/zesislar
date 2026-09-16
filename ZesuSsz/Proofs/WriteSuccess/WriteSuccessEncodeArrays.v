Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma writeSuccessPrivateEncodeLe (count : nat) (value : Z) :
  writeSuccessPrivateBytes (writeSuccessEncodeLe count value) =
  bv_to_little_endian count 8 value.
Proof.
  induction count as [|count IH] in value |- *; first reflexivity.
  rewrite /writeSuccessPrivateBytes /writeSuccessEncodeLe -/writeSuccessEncodeLe
    /bv_to_little_endian Nat2Z.inj_succ Z_to_little_endian_succ; [|lia].
  rewrite fmap_cons /=.
  rewrite Z.land_ones; [|lia]. rewrite Z.shiftr_div_pow2; [|lia].
  f_equal. apply IH.
Qed.

Lemma writeSuccessPrivateEncodeArray (count : nat) (bytes : list (bv 8)) :
  length bytes = count ->
  writeSuccessPrivateBytes (writeSuccessEncodeLe count (little_endian_to_bv 8 bytes)) = bytes.
Proof.
  intros Hlen. rewrite writeSuccessPrivateEncodeLe. apply bv_to_little_endian_to_bv; lia.
Qed.
Print Assumptions writeSuccessPrivateEncodeLe.
Print Assumptions writeSuccessPrivateEncodeArray.
