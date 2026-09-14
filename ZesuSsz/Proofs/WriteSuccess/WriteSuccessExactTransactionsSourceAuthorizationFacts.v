Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout
  WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactAuthorizationsLoopSpec.
Lemma transactions_source_authorization_loop_facts sp base transactions processed transaction rest bytes row authRest :
  Forall writeSuccessTransactionValid processed ->
  writeSuccessTransactionValid transaction ->
  transactionLoopSourceFacts sp base transactions processed (transaction :: rest) bytes ->
  writeSuccessTransactionAuthorizations transaction = row :: authRest ->
  (mapRamBase defaultMap) <= bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction) ->
  bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction) +
    Z.of_nat (length (writeSuccessTransactionAuthorizationBytes transaction)) < machineRamEnd defaultMap ->
  authorizationLoopFacts sp (transactionRowWord bytes (288 * length processed) 240)
    (bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction)) (row :: authRest) []
    row authRest (writeSuccessTransactionAuthorizationBytes transaction).
Proof.
  intros Hprocessed Hvalid Hfacts Hrows Hlow Hhigh.
  destruct Hfacts as (Htransactions & Hbytes & Hlength & Htotal & Halign & HstackLow & HstackHigh & Hrest).
  have Hcopy := Hvalid.
  destruct Hcopy as (Hsize & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
    Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount & HaccessBytes &
    HblobPointer & HblobCount & Hhashes & HblobFee & HauthPointer & HauthCount & HauthRows & Hsig).
  rewrite Htransactions in Hbytes. rewrite Hbytes.
  rewrite (exact_transaction_row_word processed transaction rest 240 Hprocessed Hvalid ltac:(lia)) HauthPointer.
  unfold authorizationLoopFacts, writeSuccessTransactionAuthorizationBytes.
  unfold writeSuccessTransactionAuthorizationBytes in Hhigh.
  rewrite Hrows in HauthCount HauthRows Hhigh |- *.
  have Hcount : (Z.of_nat (S (length authRest)) < 18446744073709551616)%Z.
  { rewrite -HauthCount. exact (proj2 (bv_unsigned_in_range 64 (writeSuccessTransactionWord transaction 248))). }
  cbn [length app]. repeat split; try assumption; try reflexivity; lia.
Qed.
Print Assumptions transactions_source_authorization_loop_facts.
