Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsLayout
  WriteSuccessExactTransactionsLiveRows.

Lemma transactions_live_current_row_facts
    sp base transactions processed transaction rest bytes :
  transactionLoopSourceFacts sp base transactions processed
    (transaction :: rest) bytes ->
  Forall writeSuccessTransactionValid transactions ->
  Forall writeSuccessTransactionValid processed /\
  writeSuccessTransactionValid transaction /\
  (forall offset, (offset + 8 <= 288)%nat ->
    transactionRowWord bytes (288 * length processed) offset =
      writeSuccessTransactionWord transaction offset) /\
  length (writeSuccessTransactionBlobBytes transaction) =
    (32 * length (writeSuccessTransactionBlobHashes transaction))%nat /\
  (Z.of_nat (length (writeSuccessTransactionBlobHashes transaction)) <
    18446744073709551616)%Z.
Proof.
  intros Hfacts Hall.
  destruct Hfacts as
    (Hrelation & Hbytes & Hlength & Htotal & Halign & HstackLow &
      HstackHigh & Hbase).
  rewrite Hrelation in Hall.
  apply Forall_app in Hall as [Hprocessed Hremaining].
  have Hvalid := Forall_inv Hremaining.
  have HvalidCopy := Hvalid.
  destruct HvalidCopy as
    (Hsize & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
     Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount &
     HaccessBytes & HblobPointer & HblobCount & Hhashes & HblobFee &
     HauthPointer & HauthCount & HauthRows & HV & HR & HS).
  have Hrow offset (Hoffset : (offset + 8 <= 288)%nat) :
    transactionRowWord bytes (288 * length processed) offset =
    writeSuccessTransactionWord transaction offset.
  { rewrite Hbytes Hrelation. apply exact_transaction_row_word; assumption. }
  have HblobLength : length (writeSuccessTransactionBlobBytes transaction) =
    (32 * length (writeSuccessTransactionBlobHashes transaction))%nat.
  { apply fixed_byte_rows_length. exact Hhashes. }
  have HblobBound :
    (Z.of_nat (length (writeSuccessTransactionBlobHashes transaction)) <
      18446744073709551616)%Z.
  { rewrite -HblobCount.
    exact (proj2 (bv_unsigned_in_range 64
      (writeSuccessTransactionWord transaction 232))). }
  repeat split; assumption.
Qed.
Print Assumptions transactions_live_current_row_facts.
