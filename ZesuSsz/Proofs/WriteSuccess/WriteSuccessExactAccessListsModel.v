Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.

Lemma access_entry_exact_events sp entry tail :
  writeSuccessExactAccessEntryEvents sp entry tail =
  writeOutputEvents (sp + BV 64 1760)%bv (BV 64 20)
    (take 20 (drop 16 (writeSuccessAccessEntryBytes entry)))
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (Z.of_nat (writeSuccessAccessEntryStorageCount entry))))
      (writeSuccessExactStorageKeysEvents sp 0
        (writeSuccessAccessEntryStorageCount entry)
        (writeSuccessAccessEntryStorageBytes entry) tail)).
Proof.
  unfold writeSuccessExactAccessEntryEvents, writeSuccessExactStorageKeysEvents.
  cbn [writeSuccessAccessObservation observationAccessAddress observationStorageKeys].
  unfold writeSuccessBytesAt. rewrite writeSuccessPrivatePublicBytes.
  rewrite Nat.mul_0_r drop_0. reflexivity.
Qed.
Print Assumptions access_entry_exact_events.
