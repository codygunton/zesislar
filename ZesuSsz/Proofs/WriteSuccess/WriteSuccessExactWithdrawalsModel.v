Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsPhases WriteSuccessRepresentation WriteSuccessEncodeFragments
  WriteSuccessOutputSemantic WriteSuccessOutputDescriptors.

Definition writeSuccessExactWithdrawalPayloads (rows : list (list (bv 8))) : list (list (bv 8)) :=
  map writeSuccessPrivateBytes (concat (map writeSuccessWithdrawalFragments
    (map writeSuccessWithdrawalObservationOfBytes rows))).
Fixpoint writeSuccessExactWithdrawalEvents (sp : bv 64) (rows : list (list (bv 8)))
    (tail : spec) : spec :=
  match rows with
  | [] => tail
  | row :: rest => withdrawalExactPhaseEvents 0 sp row (writeSuccessExactWithdrawalEvents sp rest tail)
  end.

Lemma withdrawal_rows_events_canonical sp rows tail :
  writeSuccessExactWithdrawalEvents sp rows tail =
  writeOutputPayloadsSpec (writeSuccessWithdrawalsItemDescriptors sp (length rows))
    (writeSuccessExactWithdrawalPayloads rows) tail.
Proof.
  induction rows as [|row rest IH]; first reflexivity.
  change (withdrawalExactPhaseEvents 0 sp row (writeSuccessExactWithdrawalEvents sp rest tail) =
    writeOutputPayloadsSpec
      (writeSuccessWithdrawalsItemDescriptors sp 1 ++ writeSuccessWithdrawalsItemDescriptors sp (length rest))
      (map writeSuccessPrivateBytes (writeSuccessWithdrawalFragments (writeSuccessWithdrawalObservationOfBytes row)) ++
        writeSuccessExactWithdrawalPayloads rest) tail).
  rewrite writeOutputPayloadsSpec_app; last reflexivity.
  rewrite IH. reflexivity.
Qed.
Print Assumptions withdrawal_rows_events_canonical.
