Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma exact_transaction_row_slice prefix transaction suffix offset width :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  (offset + width <= 288)%nat ->
  take width (drop (288 * length prefix + offset)
    (writeSuccessTransactionsBytes (prefix ++ transaction :: suffix))) =
  take width (drop offset (writeSuccessTransactionBytes transaction)).
Proof.
  intros Hprefix [Hlength Hvalid] Hrange.
  have Happend first second : writeSuccessTransactionsBytes (first ++ second) =
    writeSuccessTransactionsBytes first ++ writeSuccessTransactionsBytes second.
  { induction first; cbn; [reflexivity | rewrite IHfirst app_assoc; reflexivity]. }
  have HprefixLength : length (writeSuccessTransactionsBytes prefix) = (288 * length prefix)%nat.
  { induction Hprefix as [|head rest [HheadLength Hhead] Hrest IH]; first reflexivity.
    cbn. rewrite app_length HheadLength IH. lia. }
  rewrite -drop_drop Happend -HprefixLength drop_app_length.
  cbn [writeSuccessTransactionsBytes].
  rewrite drop_app_le; [|lia]. rewrite take_app_le; [reflexivity |].
  rewrite length_drop Hlength. lia.
Qed.
Print Assumptions exact_transaction_row_slice.
