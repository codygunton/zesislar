Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment18FrameDefs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment18FrameExtract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment18FrameArray.

Lemma write_success_storage_keys_segment18_prepare
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  writeSuccessStorageKeysLoopSpec x19 P -∗
  ∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec) (byte : bv 8),
    writeSuccessStorageKeysLbuState P "x1" 0 3 x19 sp pointer base total
      processed remaining bytes tail byte.
Proof.
  iIntros "Hentry".
  iApply (write_success_storage_keys_segment18_array x19 P).
  iApply (write_success_storage_keys_segment18_extract x19 P).
  iExact "Hentry".
Qed.
