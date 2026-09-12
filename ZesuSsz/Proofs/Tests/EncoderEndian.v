Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Lemma test_encoder_endian_finish (value : Z) :
  exists byte rest,
    Z_to_little_endian 8 8 value = byte :: rest /\
    Z_to_bv 8 byte = Z_to_bv 8 (value `mod` 256) /\
    map (Z_to_bv 8) rest =
      writeSuccessPrivateBytes (writeSuccessEncodeLe 7 (value `div` 256)).
Proof. zesu_finish_little_endian. Qed.

Print Assumptions test_encoder_endian_finish.
