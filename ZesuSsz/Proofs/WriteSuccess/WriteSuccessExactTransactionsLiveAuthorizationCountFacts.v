Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsLiveRows.

Lemma transactions_live_authorization_count_facts transaction bytes index :
  writeSuccessTransactionValid transaction ->
  transactionRowWord bytes index 248 =
    writeSuccessTransactionWord transaction 248 ->
  transactionRowWord bytes index 248 =
    Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionAuthorizations transaction))) /\
  (Z.of_nat (length (writeSuccessTransactionAuthorizations transaction)) <
    18446744073709551616)%Z /\
  length (writeSuccessTransactionAuthorizationBytes transaction) =
    (144 * length (writeSuccessTransactionAuthorizations transaction))%nat.
Proof.
  intros Hvalid Hrow.
  have Hcopy := Hvalid.
  destruct Hcopy as
    (Hsize & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
     Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount &
     HaccessBytes & HblobPointer & HblobCount & Hhashes & HblobFee &
     HauthPointer & HauthCount & HauthRows & HV & HR & HS).
  have Hbound :
    (Z.of_nat (length (writeSuccessTransactionAuthorizations transaction)) <
      18446744073709551616)%Z.
  { rewrite -HauthCount.
    exact (proj2 (bv_unsigned_in_range 64
      (writeSuccessTransactionWord transaction 248))). }
  repeat split.
  - rewrite Hrow. apply bv_eq.
    rewrite Z_to_bv_small; [exact HauthCount |].
    split; [lia | exact Hbound].
  - exact Hbound.
  - apply fixed_byte_rows_length. exact HauthRows.
Qed.
Print Assumptions transactions_live_authorization_count_facts.
