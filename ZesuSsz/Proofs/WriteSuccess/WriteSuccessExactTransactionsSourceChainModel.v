Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsTypeTailModel
  WriteSuccessExactTransactionsSourceFieldEvents WriteSuccessExactTransactionsSourceFieldModel
  WriteSuccessExactTransactionsChainTailModel WriteSuccessExactTransactionsBlobCountTailModel
  WriteSuccessExactBooleanSpec WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_source_chain_model sp prefix transaction rest tail :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  let bytes := writeSuccessTransactionsBytes (prefix ++ transaction :: rest) in
  let index := (288 * length prefix)%nat in
  let next := transactionSourceAfterChainEvents sp bytes index
    (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessExactTransactionAfterBlobCountEvents sp transaction tail) in
  (match writeSuccessTransactionChainId transaction with
   | None => writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
       (writeSuccessBooleanWordPayload (BV 64 0)) next
   | Some _ => writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
       (writeSuccessBooleanWordPayload (BV 64 1))
       (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
         (writeSuccessPrivateBytes (writeSuccessEncodeU64
           (bv_unsigned (transactionRowWord bytes index 160)))) next)
   end) = writeSuccessExactTransactionAfterTypeEvents sp transaction tail.
Proof.
  intros Hprefix Hvalid. cbn zeta.
  rewrite (transactions_source_field_model sp prefix transaction rest tail Hprefix Hvalid)
    transactions_exact_chain_tail.
  have Hchain := proj1 (proj2 (proj2 Hvalid)).
  destruct (writeSuccessTransactionChainId transaction) as [chain|] eqn:Hoption.
  - cbn in Hchain. destruct Hchain as [Htag Hvalue].
    rewrite (exact_transaction_row_word prefix transaction rest 160 Hprefix Hvalid ltac:(lia))
      Hvalue (writeSuccessBooleanWordPayload_encoder true). reflexivity.
  - rewrite (writeSuccessBooleanWordPayload_encoder false). reflexivity.
Qed.
Print Assumptions transactions_source_chain_model.
