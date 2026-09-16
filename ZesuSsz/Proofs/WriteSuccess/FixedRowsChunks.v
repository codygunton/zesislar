Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysModel.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessRepresentation WriteSuccessOutputSemantic.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma fixed_rows_chunks width (rows : list (list (bv 8))) :
  Forall (fun row => length row = width) rows ->
  map writeSuccessPrivateBytes (writeSuccessFixedChunks width (length rows) (concat rows)) = rows.
Proof.
  intros Hall. induction Hall as [|row rows Hrow Hrows IH]; first reflexivity.
  cbn [length concat].
  rewrite writeSuccessFixedChunks_cons. cbn [List.map].
  unfold writeSuccessBytesAt. rewrite drop_0 writeSuccessPrivatePublicBytes.
  rewrite (take_app_length' row (concat rows) width ltac:(lia)).
  rewrite (drop_app_length' row (concat rows) width ltac:(lia)).
  rewrite IH. reflexivity.
Qed.
Print Assumptions fixed_rows_chunks.
