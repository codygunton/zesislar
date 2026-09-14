Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout
  WriteSuccessExactTransactionsSourceSuffixModel WriteSuccessExactTransactionsAuthorizationTailModel
  WriteSuccessExactEncoderU256Spec WriteSuccessRepresentation.

Lemma transactions_exact_signature_tail sp prefix transaction rest tail :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  transactionSourceSignatureEvents sp
    (writeSuccessTransactionsBytes (prefix ++ transaction :: rest)) (288 * length prefix) tail =
  writeSuccessExactTransactionAfterAuthorizationEvents sp transaction tail.
Proof.
  intros Hprefix Hvalid.
  have Hcopy := Hvalid.
  destruct Hcopy as (Hlength & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
    Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount & HaccessBytes &
    HblobPointer & HblobCount & Hhashes & HblobFee & HauthPointer & HauthCount & HauthRows & HV & HR & HS).
  unfold transactionSourceSignatureEvents, writeSuccessExactTransactionAfterAuthorizationEvents.
  rewrite !(exact_transaction_row_word prefix transaction rest _ Hprefix Hvalid); [|lia..].
  rewrite HV HR HS !writeSuccessU256WordsPayload_encoder.
  cbn [writeSuccessWordsValue]. rewrite !Z.mul_0_r !Z.add_0_r. reflexivity.
Qed.
Print Assumptions transactions_exact_signature_tail.
