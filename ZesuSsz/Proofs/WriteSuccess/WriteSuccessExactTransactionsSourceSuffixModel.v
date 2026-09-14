Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsAuthorizationTailModel
  WriteSuccessExactTransactionsBlobTailModel WriteSuccessExactAuthorizationsModel
  WriteSuccessExactEncoderU128 WriteSuccessExactEncoderU256Spec
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionSourceSignatureEvents sp bytes index tail : spec :=
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned (transactionRowWord bytes index 256))))
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload (transactionRowWord bytes index 96)
        (transactionRowWord bytes index 104) (transactionRowWord bytes index 112)
        (transactionRowWord bytes index 120))
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeSuccessU256WordsPayload (transactionRowWord bytes index 128)
          (transactionRowWord bytes index 136) (transactionRowWord bytes index 144)
          (transactionRowWord bytes index 152)) tail)).

Definition transactionSourceAfterBlobEvents sp bytes index rows tail : spec :=
  writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
    (writeSuccessU128WordsPayload (transactionRowWord bytes index 80) (transactionRowWord bytes index 88))
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned (transactionRowWord bytes index 248))))
      (writeSuccessExactAuthorizationEvents sp rows (transactionSourceSignatureEvents sp bytes index tail))).

Lemma transactions_source_suffix_model sp prefix transaction rest tail :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  transactionSourceAfterBlobEvents sp
    (writeSuccessTransactionsBytes (prefix ++ transaction :: rest)) (288 * length prefix)
    (writeSuccessTransactionAuthorizations transaction) tail =
  writeSuccessExactTransactionAfterBlobEvents sp transaction tail.
Proof.
  intros Hprefix Hvalid.
  have Hcopy := Hvalid.
  destruct Hcopy as (Hlength & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
    Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount & HaccessBytes &
    HblobPointer & HblobCount & Hhashes & HblobFee & HauthPointer & HauthCount & HauthRows & HV & HR & HS).
  rewrite transactions_exact_authorization_count_tail.
  unfold transactionSourceAfterBlobEvents, transactionSourceSignatureEvents,
    writeSuccessExactTransactionAfterAuthorizationCountEvents,
    writeSuccessExactTransactionAfterAuthorizationEvents.
  rewrite !(exact_transaction_row_word prefix transaction rest _ Hprefix Hvalid); [|lia..].
  rewrite HauthCount HV -HblobFee HR HS.
  rewrite writeSuccessU128WordsPayload_encoder !writeSuccessU256WordsPayload_encoder.
  cbn [writeSuccessPairValue writeSuccessWordsValue].
  rewrite !Z.mul_0_r !Z.add_0_r. reflexivity.
Qed.
Print Assumptions transactions_source_suffix_model.
