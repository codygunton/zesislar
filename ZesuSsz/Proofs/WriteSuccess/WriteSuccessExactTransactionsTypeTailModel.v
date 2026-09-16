Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSpec WriteSuccessTransactionsSpec
  WriteSuccessOutputDescriptors WriteSuccessOutputSemantic
  WriteSuccessEncodeFragments WriteSuccessRepresentation WriteSuccessObservation.

Definition writeSuccessExactTransactionAfterTypeEvents
    (sp : bv 64) (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  writeOutputPayloadsSpec (tl (writeSuccessTransactionDescriptors sp transaction))
    (tl (map writeSuccessPrivateBytes (writeSuccessTransactionFragments
      (writeSuccessTransactionObservationOfNative transaction)))) tail.

Lemma transactions_exact_type_tail sp transaction rest tail :
  writeSuccessExactTransactionsEvents sp (transaction :: rest) tail =
  writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
    [writeSuccessTransactionType transaction]
    (writeSuccessExactTransactionAfterTypeEvents sp transaction
      (writeSuccessExactTransactionsEvents sp rest tail)).
Proof.
  replace (transaction :: rest) with ([transaction] ++ rest) by reflexivity.
  rewrite writeSuccessExactTransactionsEvents_app.
  unfold writeSuccessExactTransactionsEvents at 1.
  unfold writeSuccessExactTransactionsPayloads.
  cbn [writeSuccessTransactionsDescriptors writeSuccessTransactionDescriptors
    writeSuccessTransactionFragments writeSuccessTransactionObservationOfNative
    observationTransactionType map concat app length].
  unfold writeSuccessExactTransactionAfterTypeEvents.
  cbn [writeSuccessTransactionDescriptors writeSuccessTransactionFragments
    writeSuccessTransactionObservationOfNative observationTransactionType map app tl
    writeOutputPayloadsSpec writeSuccessPrivateBytes].
  have Htype : Z_to_bv 8 (bv_unsigned (writeSuccessTransactionType transaction) `mod` 256) =
      writeSuccessTransactionType transaction by bv_solve.
  rewrite Htype !app_nil_r. reflexivity.
Qed.
Print Assumptions transactions_exact_type_tail.
