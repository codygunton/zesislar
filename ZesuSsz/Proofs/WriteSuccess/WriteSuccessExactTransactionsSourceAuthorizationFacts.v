Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout WriteSuccessExactTransactionsGasLoads WriteSuccessExactAuthorizationsLoopSpec.
Lemma transactions_source_authorization_initial_facts
 sp transactions processed transaction rest bytes row authRest :
 Forall writeSuccessTransactionValid processed ->
 writeSuccessTransactionValid transaction ->
 transactions = processed ++ transaction :: rest ->
 bytes = writeSuccessTransactionsBytes transactions ->
 writeSuccessTransactionAuthorizations transaction = row :: authRest ->
 bv_unsigned sp `mod` 16 = 0 ->
 mapRamBase defaultMap <= bv_unsigned sp - 48 ->
 bv_unsigned sp + 1896 < machineRamEnd defaultMap ->
 mapRamBase defaultMap <= bv_unsigned (transactionRowWord bytes (288 * length processed) 240) ->
 bv_unsigned (transactionRowWord bytes (288 * length processed) 240) + Z.of_nat (length (writeSuccessTransactionAuthorizationBytes transaction)) < machineRamEnd defaultMap ->
 authorizationLoopFacts sp (transactionRowWord bytes (288 * length processed) 240)
  (bv_unsigned (transactionRowWord bytes (288 * length processed) 240))
  (row :: authRest) [] row authRest (writeSuccessTransactionAuthorizationBytes transaction) /\
 transactionRowWord bytes (288 * length processed) 248 = Z_to_bv 64 (Z.of_nat (S (length authRest))).
Proof.
 intros Hprefix Hvalid Hrelation Hbytes Hrows Halign Hlow Hhigh HbaseLow HbaseHigh.
 have Hrow : forall offset, (offset + 8 <= 288)%nat ->
 transactionRowWord bytes (288 * length processed) offset = writeSuccessTransactionWord transaction offset.
 {
 intros offset Hoffset.
 rewrite Hbytes Hrelation.
 apply exact_transaction_row_word; assumption.
 }
 have HrowsValid : Forall (fun authorization => length authorization = 144%nat) (row :: authRest).
 {
 rewrite -Hrows.
 unfold writeSuccessTransactionValid in Hvalid.
 tauto.
 }
 have Hcount : bv_unsigned (transactionRowWord bytes (288 * length processed) 248) = Z.of_nat (S (length authRest)).
 {
 rewrite Hrow; last lia.
 have Hcanonical : bv_unsigned (writeSuccessTransactionWord transaction 248) = Z.of_nat (length (writeSuccessTransactionAuthorizations transaction)).
 {
 unfold writeSuccessTransactionValid in Hvalid.
 tauto.
 }
 rewrite Hrows in Hcanonical.
 exact Hcanonical.
 }
 have HcountBound : (Z.of_nat (S (length authRest)) < 18446744073709551616)%Z.
 {
 rewrite -Hcount.
 exact (proj2 (bv_unsigned_in_range 64 (transactionRowWord bytes (288 * length processed) 248))).
 }
 split.
 -
 unfold authorizationLoopFacts.
 repeat split; try assumption.
 +
 unfold writeSuccessTransactionAuthorizationBytes.
 rewrite Hrows.
 reflexivity.
 +
 cbn.
 lia.
 -
 apply bv_eq.
 rewrite Z_to_bv_small; [exact Hcount |].
 split; [lia | exact HcountBound].
Qed.
Print Assumptions transactions_source_authorization_initial_facts.
