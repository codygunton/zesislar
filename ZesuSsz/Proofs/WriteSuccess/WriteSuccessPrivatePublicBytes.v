Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Lemma writeSuccessPrivatePublicBytes (bytes : list (bv 8)) :
  writeSuccessPrivateBytes (writeSuccessPublicBytes bytes) = bytes.
Proof.
  unfold writeSuccessPrivateBytes, writeSuccessPublicBytes.
  induction bytes as [|byte bytes IH]; first reflexivity.
  cbn. rewrite Z_to_bv_bv_unsigned IH. reflexivity.
Qed.
Print Assumptions writeSuccessPrivatePublicBytes.
