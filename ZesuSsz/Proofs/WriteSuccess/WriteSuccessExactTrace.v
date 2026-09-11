Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeFragments.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

Definition writeSuccessAllDescriptors
    (sp : bv 64) (values : list (bv 64))
    (transactions : list writeSuccessTransaction) (withdrawalsCount : nat)
    (post : WriteSuccessPostTransactionData) : list WriteOutputDescriptor :=
  writeSuccessMainDescriptors sp values transactions ++
  writeSuccessAfterTransactionsDescriptors sp withdrawalsCount post.

Definition writeSuccessExactObservation
    (decodedBytes : list (bv 8)) (values : list (bv 64))
    (payload : list (bv 8)) (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData) :
    WriteSuccessObservation :=
  writeSuccessNativeObservation decodedBytes values payload transactions
    rawTransactions withdrawalsBytes withdrawalsCount post.

Definition writeSuccessExactPayloads
    (decodedBytes : list (bv 8)) (values : list (bv 64))
    (payload : list (bv 8)) (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData) :
    list (list (bv 8)) :=
  map writeSuccessPrivateBytes
    (writeSuccessEncodeFragments
      (writeSuccessExactObservation decodedBytes values payload transactions
        rawTransactions withdrawalsBytes withdrawalsCount post)).

Definition writeSuccessExactEvents
    (sp : bv 64) (decodedBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (transactions : list writeSuccessTransaction)
    (rawTransactions : list ByteListItem) (withdrawalsBytes : list (bv 8))
    (withdrawalsCount : nat) (post : WriteSuccessPostTransactionData)
    (tail : spec) : spec :=
  writeOutputPayloadsSpec
    (writeSuccessAllDescriptors sp values transactions withdrawalsCount post)
    (writeSuccessExactPayloads decodedBytes values payload transactions
      rawTransactions withdrawalsBytes withdrawalsCount post)
    tail.
