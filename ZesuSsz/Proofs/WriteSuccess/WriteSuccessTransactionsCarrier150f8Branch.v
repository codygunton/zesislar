From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierChunk150f0Entry.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsAt150f8CarrierSomeSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (chainId sp : bv 64) (base : Z)
      (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    ⌜writeSuccessTransactionChainId transaction = Some chainId⌝ ∗
    □ ⌜writeSuccessTransactionByte transaction 168 <> BV 8 0⌝ ∗
    writeSuccessTransactionsAt150f8CarrierCallBlockFixed P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I.

Definition writeSuccessTransactionsAt150f8CarrierNoneSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    ⌜writeSuccessTransactionChainId transaction = None⌝ ∗
    □ ⌜writeSuccessTransactionByte transaction 168 = BV 8 0⌝ ∗
    writeSuccessTransactionsAt150f8CarrierCallBlockFixed P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150f8CarrierSomeSpec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150f8CarrierNoneSpec) := I.

Lemma write_success_transactions_carrier_150f8_branch
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsAt150f8CarrierCallSpec P -∗
  writeSuccessTransactionsAt150f8CarrierSomeSpec P ∨
  writeSuccessTransactionsAt150f8CarrierNoneSpec P.
Proof.
  rewrite /writeSuccessTransactionsAt150f8CarrierCallSpec.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix
      tail first second third fourth items) "Hentry".
  iEval (unfold writeSuccessTransactionsAt150f8CarrierCallBlockFixed)
    in "Hentry".
  iDestruct "Hentry" as "(Hmachine & Hmmio & Htrace & Hframe & _)".
  iEval (unfold writeSuccessTransactions150ecCarrierCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(H34 & Hscratch & Harray & Hprefix & Hsuffix & Hprocessed & Hdata &
      Hrest & Hremaining & HP & Hinvariant & Hexit & HloadFacts & _)".
  iEval (unfold writeSuccessTransactionRestOwn) in "Hrest".
  iDestruct "Hrest" as
    "(HaccessBytes & Haccess & Hblob & Hauthorization & %Hvalid & _)".
  have HvalidParts := Hvalid.
  unfold writeSuccessTransactionValid in HvalidParts.
  destruct HvalidParts as (Hlength & Htype & Hchain & HvalidTail).
  iAssert (writeSuccessTransactionRestOwn transaction)%I
    with "[HaccessBytes Haccess Hblob Hauthorization]" as "Hrest".
  { rewrite /writeSuccessTransactionRestOwn.
    iFrame. iSplit; first (iPureIntro; exact Hvalid). done. }
  iAssert (writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)%I
    with "[H34 Hscratch Harray Hprefix Hsuffix Hprocessed Hdata Hrest
      Hremaining HP Hinvariant Hexit HloadFacts]" as "Hframe".
  { rewrite /writeSuccessTransactions150ecCarrierCallFrame. iFrame. }
  destruct (writeSuccessTransactionChainId transaction)
    as [chainId |] eqn:HchainId.
  - cbn in Hchain. destruct Hchain as (Htag & Hword).
    iLeft.
    rewrite /writeSuccessTransactionsAt150f8CarrierSomeSpec
      /writeSuccessTransactionsAt150f8CarrierCallBlockFixed.
    iExists chainId, sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail, first, second, third, fourth, items.
    iFrame.
    repeat iSplit.
    + iPureIntro. exact HchainId.
    + iModIntro. iPureIntro. exact Htag.
  - cbn in Hchain.
    iRight.
    rewrite /writeSuccessTransactionsAt150f8CarrierNoneSpec
      /writeSuccessTransactionsAt150f8CarrierCallBlockFixed.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail, first, second, third, fourth, items.
    iFrame.
    repeat iSplit.
    + iPureIntro. exact HchainId.
    + iModIntro. iPureIntro. exact Hchain.
Qed.
