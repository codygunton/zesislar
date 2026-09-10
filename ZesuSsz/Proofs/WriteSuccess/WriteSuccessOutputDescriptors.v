Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.

Import ListNotations.

Fixpoint writeSuccessRepeatedDescriptors
    (data size : bv 64) (count : nat) : list WriteOutputDescriptor :=
  match count with
  | O => []
  | S count => (data, size) ::
      writeSuccessRepeatedDescriptors data size count
  end.

Lemma writeSuccessRepeatedDescriptors_spec data size count tail :
  writeOutputDescriptorsSpec
      (writeSuccessRepeatedDescriptors data size count) tail =
  Nat.iter count (writeOutputEvents data size) tail.
Proof.
  induction count; simpl; [reflexivity |].
  rewrite IHcount. reflexivity.
Qed.

Definition writeSuccessHeaderDescriptors
    (sp : bv 64) : list WriteOutputDescriptor := [
  (BV 64 0x179c5, BV 64 6);
  ((sp + BV 64 1184)%bv, BV 64 32);
  ((sp + BV 64 1216)%bv, BV 64 20);
  ((sp + BV 64 1236)%bv, BV 64 32);
  ((sp + BV 64 1268)%bv, BV 64 32);
  ((sp + BV 64 1300)%bv, BV 64 256);
  ((sp + BV 64 1556)%bv, BV 64 32)
].

Lemma writeSuccessHeaderDescriptors_spec sp tail :
  writeOutputDescriptorsSpec (writeSuccessHeaderDescriptors sp) tail =
  writeSuccessHeaderEvents sp tail.
Proof. reflexivity. Qed.

Definition writeSuccessValueDescriptors
    (sp : bv 64) (values : list (bv 64)) : list WriteOutputDescriptor := [
  ((sp - BV 64 16)%bv, BV 64 8);
  ((sp - BV 64 16)%bv, BV 64 8);
  ((sp - BV 64 16)%bv, BV 64 8);
  ((sp - BV 64 16)%bv, BV 64 8);
  ((sp - BV 64 48)%bv, BV 64 8);
  (writeSuccessValueWord values 4, writeSuccessValueWord values 5);
  ((sp - BV 64 16)%bv, BV 64 8);
  ((sp + BV 64 1588)%bv, BV 64 32);
  ((sp - BV 64 16)%bv, BV 64 8)
].

Lemma writeSuccessValueDescriptors_spec sp values tail :
  writeOutputDescriptorsSpec (writeSuccessValueDescriptors sp values) tail =
  writeSuccessValueEvents sp values tail.
Proof. reflexivity. Qed.

Fixpoint byteListItemDescriptors
    (sp : bv 64) (items : list ByteListItem) : list WriteOutputDescriptor :=
  match items with
  | [] => []
  | item :: rest =>
      ((sp - BV 64 48)%bv, BV 64 8) ::
      (byteListData item, byteListSize item) ::
      byteListItemDescriptors sp rest
  end.

Lemma byteListItemDescriptors_spec sp items tail :
  writeOutputDescriptorsSpec (byteListItemDescriptors sp items) tail =
  byteListItemEvents sp items tail.
Proof.
  induction items as [|item rest IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Definition writeSuccessBytesDescriptors
    (sp data size : bv 64) : list WriteOutputDescriptor := [
  ((sp - BV 64 48)%bv, BV 64 8);
  (data, size)
].

Lemma writeSuccessBytesDescriptors_spec sp data size tail :
  writeOutputDescriptorsSpec (writeSuccessBytesDescriptors sp data size) tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (writeOutputEvents data size tail).
Proof. reflexivity. Qed.

Definition writeSuccessByteListsDescriptors
    (sp : bv 64) (items : list ByteListItem) :
    list WriteOutputDescriptor :=
  ((sp - BV 64 48)%bv, BV 64 8) ::
  byteListItemDescriptors (sp - BV 64 32)%bv items.

Lemma writeSuccessByteListsDescriptors_spec sp items tail :
  writeOutputDescriptorsSpec
      (writeSuccessByteListsDescriptors sp items) tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (byteListItemEvents (sp - BV 64 32)%bv items tail).
Proof.
  simpl. rewrite byteListItemDescriptors_spec. reflexivity.
Qed.

Fixpoint writeSuccessWithdrawalsItemDescriptors
    (sp : bv 64) (count : nat) : list WriteOutputDescriptor :=
  match count with
  | O => []
  | S count =>
      [((sp - BV 64 16)%bv, BV 64 8);
       ((sp - BV 64 16)%bv, BV 64 8);
       ((sp + BV 64 1768)%bv, BV 64 20);
       ((sp - BV 64 16)%bv, BV 64 8)] ++
      writeSuccessWithdrawalsItemDescriptors sp count
  end.

Lemma writeSuccessWithdrawalsItemDescriptors_spec sp count tail :
  writeOutputDescriptorsSpec
      (writeSuccessWithdrawalsItemDescriptors sp count) tail =
  writeSuccessWithdrawalsEvents sp count tail.
Proof.
  induction count as [|count IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Definition writeSuccessWithdrawalsDescriptors
    (sp : bv 64) (count : nat) : list WriteOutputDescriptor :=
  ((sp - BV 64 16)%bv, BV 64 8) ::
  writeSuccessWithdrawalsItemDescriptors sp count.

Lemma writeSuccessWithdrawalsDescriptors_spec sp count tail :
  writeOutputDescriptorsSpec
      (writeSuccessWithdrawalsDescriptors sp count) tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessWithdrawalsEvents sp count tail).
Proof.
  simpl. rewrite writeSuccessWithdrawalsItemDescriptors_spec. reflexivity.
Qed.

Definition writeSuccessHashesDescriptors
    (sp : bv 64) (count : nat) : list WriteOutputDescriptor :=
  ((sp - BV 64 16)%bv, BV 64 8) ::
  writeSuccessRepeatedDescriptors
    (sp + BV 64 1744)%bv (BV 64 32) count.

Lemma writeSuccessHashesDescriptors_spec sp count tail :
  writeOutputDescriptorsSpec (writeSuccessHashesDescriptors sp count) tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessHashesEvents sp count tail).
Proof.
  unfold writeSuccessHashesDescriptors. simpl.
  rewrite writeSuccessRepeatedDescriptors_spec.
  f_equal.
  induction count as [|count IH]; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Definition writeSuccessStorageKeysDescriptors
    (sp : bv 64) (count : nat) : list WriteOutputDescriptor :=
  writeSuccessRepeatedDescriptors
    (sp + BV 64 1712)%bv (BV 64 32) count.

Lemma writeSuccessStorageKeysDescriptors_spec sp count tail :
  writeOutputDescriptorsSpec
      (writeSuccessStorageKeysDescriptors sp count) tail =
  writeSuccessStorageKeysEvents sp count tail.
Proof.
  induction count; simpl; [reflexivity |].
  rewrite IHcount. reflexivity.
Qed.

Fixpoint writeSuccessAccessListsDescriptors
    (sp : bv 64) (entries : list writeSuccessAccessEntry) :
    list WriteOutputDescriptor :=
  match entries with
  | [] => []
  | entry :: rest =>
      [((sp + BV 64 1760)%bv, BV 64 20);
       ((sp - BV 64 16)%bv, BV 64 8)] ++
      writeSuccessStorageKeysDescriptors sp
        (writeSuccessAccessEntryStorageCount entry) ++
      writeSuccessAccessListsDescriptors sp rest
  end.

Lemma writeSuccessAccessListsDescriptors_spec sp entries tail :
  writeOutputDescriptorsSpec
      (writeSuccessAccessListsDescriptors sp entries) tail =
  writeSuccessAccessListsEvents sp entries tail.
Proof.
  induction entries as [|entry rest IH]; simpl; [reflexivity |].
  rewrite !writeOutputDescriptorsSpec_app.
  rewrite writeSuccessStorageKeysDescriptors_spec IH.
  reflexivity.
Qed.

Definition writeSuccessBlobHashesDescriptors
    (sp : bv 64) (count : nat) : list WriteOutputDescriptor :=
  writeSuccessRepeatedDescriptors
    (sp + BV 64 1680)%bv (BV 64 32) count.

Lemma writeSuccessBlobHashesDescriptors_spec sp count tail :
  writeOutputDescriptorsSpec
      (writeSuccessBlobHashesDescriptors sp count) tail =
  writeSuccessBlobHashesEvents sp count tail.
Proof.
  induction count; simpl; [reflexivity |].
  rewrite IHcount. reflexivity.
Qed.

Fixpoint writeSuccessAuthorizationsDescriptors
    (sp : bv 64) (count : nat) : list WriteOutputDescriptor :=
  match count with
  | O => []
  | S count =>
      [((sp - BV 64 48)%bv, BV 64 32);
       ((sp + BV 64 1856)%bv, BV 64 20);
       ((sp - BV 64 16)%bv, BV 64 8);
       ((sp - BV 64 16)%bv, BV 64 8);
       ((sp - BV 64 48)%bv, BV 64 32);
       ((sp - BV 64 48)%bv, BV 64 32)] ++
      writeSuccessAuthorizationsDescriptors sp count
  end.

Lemma writeSuccessAuthorizationsDescriptors_spec sp count tail :
  writeOutputDescriptorsSpec
      (writeSuccessAuthorizationsDescriptors sp count) tail =
  writeSuccessAuthorizationsEvents sp count tail.
Proof.
  induction count; simpl; [reflexivity |].
  rewrite IHcount. reflexivity.
Qed.

Definition writeSuccessOptionalU64Descriptors
    (sp : bv 64) (value : option (bv 64)) : list WriteOutputDescriptor :=
  match value with
  | None => [((sp - BV 64 9)%bv, BV 64 1)]
  | Some _ =>
      [((sp - BV 64 25)%bv, BV 64 1);
       ((sp - BV 64 16)%bv, BV 64 8)]
  end.

Lemma writeSuccessOptionalU64Descriptors_spec sp value tail :
  writeOutputDescriptorsSpec
      (writeSuccessOptionalU64Descriptors sp value) tail =
  writeSuccessOptionalU64Events sp value tail.
Proof. destruct value; reflexivity. Qed.

Definition writeSuccessOptionalU128Descriptors
    (sp : bv 64) (value : option (bv 64 * bv 64)) :
    list WriteOutputDescriptor :=
  match value with
  | None => [((sp - BV 64 9)%bv, BV 64 1)]
  | Some _ =>
      [((sp - BV 64 9)%bv, BV 64 1);
       ((sp - BV 64 32)%bv, BV 64 16)]
  end.

Lemma writeSuccessOptionalU128Descriptors_spec sp value tail :
  writeOutputDescriptorsSpec
      (writeSuccessOptionalU128Descriptors sp value) tail =
  writeSuccessOptionalU128Events sp value tail.
Proof. destruct value as [[first second]|]; reflexivity. Qed.

Definition writeSuccessOptionalAddressDescriptors
    (sp : bv 64) (value : option (list (bv 8))) :
    list WriteOutputDescriptor :=
  match value with
  | None => [((sp - BV 64 9)%bv, BV 64 1)]
  | Some _ =>
      [((sp - BV 64 9)%bv, BV 64 1);
       ((sp + BV 64 1744)%bv, BV 64 20)]
  end.

Lemma writeSuccessOptionalAddressDescriptors_spec sp value tail :
  writeOutputDescriptorsSpec
      (writeSuccessOptionalAddressDescriptors sp value) tail =
  writeSuccessOptionalAddressEvents sp value tail.
Proof. destruct value; reflexivity. Qed.

Definition writeSuccessTransactionDescriptors
    (sp : bv 64) (transaction : writeSuccessTransaction) :
    list WriteOutputDescriptor :=
  [((sp + BV 64 1744)%bv, BV 64 1)] ++
  writeSuccessOptionalU64Descriptors sp
    (writeSuccessTransactionChainId transaction) ++
  [((sp - BV 64 16)%bv, BV 64 8);
   ((sp - BV 64 32)%bv, BV 64 16)] ++
  writeSuccessOptionalU128Descriptors sp
    (writeSuccessTransactionGasPriorityFee transaction) ++
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessOptionalAddressDescriptors sp
    (writeSuccessTransactionTo transaction) ++
  [((sp - BV 64 48)%bv, BV 64 32);
   ((sp - BV 64 48)%bv, BV 64 8);
   (writeSuccessTransactionDataPointer transaction,
    Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionData transaction))));
   ((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessAccessListsDescriptors sp
    (writeSuccessTransactionAccessEntries transaction) ++
  [((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessBlobHashesDescriptors sp
    (length (writeSuccessTransactionBlobHashes transaction)) ++
  [((sp - BV 64 32)%bv, BV 64 16);
   ((sp - BV 64 16)%bv, BV 64 8)] ++
  writeSuccessAuthorizationsDescriptors sp
    (length (writeSuccessTransactionAuthorizations transaction)) ++
  [((sp - BV 64 16)%bv, BV 64 8);
   ((sp - BV 64 48)%bv, BV 64 32);
   ((sp - BV 64 48)%bv, BV 64 32)].

Lemma writeSuccessTransactionDescriptors_spec sp transaction tail :
  writeOutputDescriptorsSpec
      (writeSuccessTransactionDescriptors sp transaction) tail =
  writeSuccessTransactionEvents sp transaction tail.
Proof.
  rewrite /writeSuccessTransactionDescriptors.
  rewrite !writeOutputDescriptorsSpec_app.
  rewrite writeSuccessOptionalU64Descriptors_spec.
  rewrite writeSuccessOptionalU128Descriptors_spec.
  rewrite writeSuccessOptionalAddressDescriptors_spec.
  rewrite writeSuccessAccessListsDescriptors_spec.
  rewrite writeSuccessBlobHashesDescriptors_spec.
  rewrite writeSuccessAuthorizationsDescriptors_spec.
  reflexivity.
Qed.

Fixpoint writeSuccessTransactionsDescriptors
    (sp : bv 64) (transactions : list writeSuccessTransaction) :
    list WriteOutputDescriptor :=
  match transactions with
  | [] => []
  | transaction :: rest =>
      writeSuccessTransactionDescriptors sp transaction ++
      writeSuccessTransactionsDescriptors sp rest
  end.

Lemma writeSuccessTransactionsDescriptors_spec sp transactions tail :
  writeOutputDescriptorsSpec
      (writeSuccessTransactionsDescriptors sp transactions) tail =
  writeSuccessTransactionsEvents sp transactions tail.
Proof.
  induction transactions as [|transaction rest IH].
  - reflexivity.
  - change (writeOutputDescriptorsSpec
      (writeSuccessTransactionDescriptors sp transaction ++
       writeSuccessTransactionsDescriptors sp rest) tail =
      writeSuccessTransactionEvents sp transaction
        (writeSuccessTransactionsEvents sp rest tail)).
    rewrite writeOutputDescriptorsSpec_app.
    rewrite writeSuccessTransactionDescriptors_spec IH.
    reflexivity.
Qed.

Definition writeSuccessMainDescriptors
    (sp : bv 64) (values : list (bv 64))
    (transactions : list writeSuccessTransaction) :
    list WriteOutputDescriptor :=
  writeSuccessHeaderDescriptors sp ++
  writeSuccessValueDescriptors sp values ++
  writeSuccessTransactionsDescriptors sp transactions.

Lemma writeSuccessMainDescriptors_spec sp values transactions tail :
  writeOutputDescriptorsSpec
      (writeSuccessMainDescriptors sp values transactions) tail =
  writeSuccessHeaderEvents sp
    (writeSuccessValueEvents sp values
      (writeSuccessTransactionsEvents sp transactions tail)).
Proof.
  rewrite /writeSuccessMainDescriptors !writeOutputDescriptorsSpec_app.
  rewrite writeSuccessHeaderDescriptors_spec.
  rewrite writeSuccessValueDescriptors_spec.
  rewrite writeSuccessTransactionsDescriptors_spec.
  reflexivity.
Qed.
