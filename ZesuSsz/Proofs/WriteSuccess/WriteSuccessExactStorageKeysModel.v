Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma writeSuccessPrivatePublicBytes (bytes : list (bv 8)) :
  writeSuccessPrivateBytes (writeSuccessPublicBytes bytes) = bytes.
Proof.
  unfold writeSuccessPrivateBytes, writeSuccessPublicBytes.
  induction bytes as [|byte bytes IH]; simpl; [reflexivity |].
  rewrite Z_to_bv_bv_unsigned IH. reflexivity.
Qed.
Print Assumptions writeSuccessPrivatePublicBytes.

Lemma writeSuccessFixedChunks_cons width count bytes :
  writeSuccessFixedChunks width (S count) bytes =
  writeSuccessBytesAt 0 width bytes ::
    writeSuccessFixedChunks width count (drop width bytes).
Proof.
  unfold writeSuccessFixedChunks. simpl.
  rewrite -(seq_shift count 0) map_map.
  f_equal; [rewrite Nat.mul_0_r; reflexivity |].
  apply map_ext. intros index.
  unfold writeSuccessBytesAt. rewrite drop_drop.
  replace (width * S index)%nat with (width + width * index)%nat by lia.
  reflexivity.
Qed.
Print Assumptions writeSuccessFixedChunks_cons.

Definition writeSuccessExactStorageKeysEvents (sp : bv 64)
    (processed count : nat) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeSuccessExactStorageKeyEvents sp
    (map writeSuccessPrivateBytes
      (writeSuccessFixedChunks 32 count (drop (32 * processed) bytes))) tail.

Lemma writeSuccessExactStorageKeysEvents_zero sp processed bytes tail :
  writeSuccessExactStorageKeysEvents sp processed 0 bytes tail = tail.
Proof. reflexivity. Qed.
Print Assumptions writeSuccessExactStorageKeysEvents_zero.

Lemma writeSuccessExactStorageKeysEvents_cons sp processed count bytes tail :
  writeSuccessExactStorageKeysEvents sp processed (S count) bytes tail =
  writeOutputEvents (sp + BV 64 1712)%bv (BV 64 32)
    (take 32 (drop (32 * processed) bytes))
    (writeSuccessExactStorageKeysEvents sp (S processed) count bytes tail).
Proof.
  unfold writeSuccessExactStorageKeysEvents.
  rewrite writeSuccessFixedChunks_cons.
  cbn [map writeSuccessExactStorageKeyEvents].
  unfold writeSuccessBytesAt. rewrite drop_0 writeSuccessPrivatePublicBytes.
  rewrite drop_drop.
  replace (32 * processed + 32)%nat with (32 * S processed)%nat by lia.
  reflexivity.
Qed.
Print Assumptions writeSuccessExactStorageKeysEvents_cons.
