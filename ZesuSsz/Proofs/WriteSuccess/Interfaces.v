Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

From ZesuSsz.Proofs.WriteSuccess Require Export
  WriteSuccessAccessListsBoundary151dc
  WriteSuccessAccessListsBoundary15200
  WriteSuccessAccessListsBoundary15210
  WriteSuccessAccessListsBoundary1521c
  WriteSuccessAccessListsBoundary15224
  WriteSuccessEncoderOptionalU64NoneBoundary
  WriteSuccessNativeSuffixBytesBoundaryAdapter
  WriteSuccessTransactionsBoundary10190
  WriteSuccessTransactionsBoundary10190Prepared
  WriteSuccessTransactionsBoundary14f1c
  WriteSuccessTransactionsBoundary14f20
  WriteSuccessTransactionsBoundary14f24
  WriteSuccessTransactionsBoundary14f28
  WriteSuccessTransactionsBoundary14f2c
  WriteSuccessTransactionsBoundary14f30
  WriteSuccessTransactionsBoundary14f34
  WriteSuccessTransactionsBoundary14f38
  WriteSuccessTransactionsBoundary14f3c
  WriteSuccessTransactionsBoundary14f40
  WriteSuccessTransactionsBoundary14f44
  WriteSuccessTransactionsBoundary14f48
  WriteSuccessTransactionsBoundary14f4c
  WriteSuccessTransactionsBoundary14f50
  WriteSuccessTransactionsBoundary14f54
  WriteSuccessTransactionsBoundary14f58
  WriteSuccessTransactionsBoundary14f5c
  WriteSuccessTransactionsBoundary14f60
  WriteSuccessTransactionsBoundary14f64
  WriteSuccessTransactionsBoundary14f70
  WriteSuccessTransactionsBoundary14f74
  WriteSuccessTransactionsBoundary14f78
  WriteSuccessTransactionsBoundary14f7c
  WriteSuccessTransactionsBoundary14f80
  WriteSuccessTransactionsBoundary14f84
  WriteSuccessTransactionsBoundary14f88
  WriteSuccessTransactionsBoundary14f8c
  WriteSuccessTransactionsBoundary14f90
  WriteSuccessTransactionsBoundary14f98
  WriteSuccessTransactionsBoundary14f9c
  WriteSuccessTransactionsBoundary14fa0
  WriteSuccessTransactionsBoundary14fa4
  WriteSuccessTransactionsBoundary14fa8
  WriteSuccessTransactionsBoundary14fb0
  WriteSuccessTransactionsBoundary14fb4
  WriteSuccessTransactionsBoundary14fc8
  WriteSuccessTransactionsBoundary14fe0
  WriteSuccessTransactionsBoundary14fe0Loads
  WriteSuccessTransactionsBoundary1501c
  WriteSuccessTransactionsBoundary15028
  WriteSuccessTransactionsBoundary15044
  WriteSuccessTransactionsBoundary15048
  WriteSuccessTransactionsBoundary1505c
  WriteSuccessTransactionsBoundary15078
  WriteSuccessTransactionsBoundary15088
  WriteSuccessTransactionsBoundary1508c
  WriteSuccessTransactionsBoundary15090
  WriteSuccessTransactionsBoundary15094
  WriteSuccessTransactionsBoundary15098
  WriteSuccessTransactionsBoundary1509c
  WriteSuccessTransactionsBoundary150a0
  WriteSuccessTransactionsBoundary150a4
  WriteSuccessTransactionsBoundary150a8
  WriteSuccessTransactionsBoundary150ac
  WriteSuccessTransactionsBoundary150b0
  WriteSuccessTransactionsBoundary150b4
  WriteSuccessTransactionsBoundary150b8
  WriteSuccessTransactionsBoundary150bc
  WriteSuccessTransactionsBoundary150c0
  WriteSuccessTransactionsBoundary150c4
  WriteSuccessTransactionsBoundary150c8
  WriteSuccessTransactionsBoundary150cc
  WriteSuccessTransactionsBoundary150d0
  WriteSuccessTransactionsBoundary150d4
  WriteSuccessTransactionsBoundary150d8
  WriteSuccessTransactionsBoundary150dc
  WriteSuccessTransactionsBoundary150e0
  WriteSuccessTransactionsBoundary150e4
  WriteSuccessTransactionsBoundary150e8
  WriteSuccessTransactionsBoundary150e8Adapter
  WriteSuccessTransactionsBoundary150e8Phase
  WriteSuccessTransactionsBoundary150ec
  WriteSuccessTransactionsBoundary150ecCall
  WriteSuccessTransactionsBoundary150f0
  WriteSuccessTransactionsBoundary150fc
  WriteSuccessTransactionsBoundary15100
  WriteSuccessTransactionsBoundary15104
  WriteSuccessTransactionsBoundary15108
  WriteSuccessTransactionsBoundary15118
  WriteSuccessTransactionsBoundary15148
  WriteSuccessTransactionsBoundary15154
  WriteSuccessTransactionsBoundary15158
  WriteSuccessTransactionsBoundary1519c
  WriteSuccessTransactionsBoundary151a8
  WriteSuccessTransactionsBoundary151b4
  WriteSuccessTransactionsBoundary151c4
  WriteSuccessTransactionsBoundary151d0
  WriteSuccessTransactionsBoundary153c0
  WriteSuccessTransactionsBoundary153d0
  WriteSuccessTransactionsBoundary15564
  WriteSuccessTransactionsBoundary15570
  WriteSuccessTransactionsBoundary15574
  WriteSuccessTransactionsBoundary15580
  WriteSuccessTransactionsBoundary15584
  WriteSuccessTransactionsBoundary15620
  WriteSuccessTransactionsBoundary15628
  WriteSuccessTransactionsBoundary1562c
  WriteSuccessTransactionsBoundary15640
  WriteSuccessTransactionsBoundary15644
  WriteSuccessTransactionsBoundary15658
  WriteSuccessTransactionsBoundary1565c
  WriteSuccessTransactionsBoundary15668
  WriteSuccessTransactionsBoundary15bc8Some
  WriteSuccessTransactionsBoundarySpec
  WriteSuccessTransactionsCarrierBoundary14f1c
  WriteSuccessTransactionsCarrierBoundary14f68
  WriteSuccessTransactionsCarrierBoundary14fc8
  WriteSuccessTransactionsCarrierBoundary150f0
  WriteSuccessTransactionsCarrierBoundary150fc
  WriteSuccessTransactionsCarrierBoundary15108
  WriteSuccessTransactionsCarrierBoundary15118
  WriteSuccessTransactionsCarrierBoundary15148
  WriteSuccessTransactionsCarrierBoundary1519c
  WriteSuccessTransactionsCarrierBoundary151b4
  WriteSuccessTransactionsCarrierBoundary151c4
  WriteSuccessTransactionsOptionalAddressNone15198Boundary
  WriteSuccessTransactionsOptionalAddressSome1517cBoundary
  WriteSuccessTransactionsOptionalAddressSome15190Boundary
  WriteSuccessTransactionsPost15674Boundary
  WriteSuccessTransactionsPriorityFeeNoneBoundary
  WriteSuccessTransactionsPriorityFeeSomeBoundary.

From ZesuSsz.Proofs.WriteSuccess Require Export
  WriteSuccessAccessListsSpec
  WriteSuccessAuthorizationsSpec
  WriteSuccessBlobHashesSpec
  WriteSuccessByteLists
  WriteSuccessCalls
  WriteSuccessEncoderBooleanCall
  WriteSuccessEncoderBytesCallCore
  WriteSuccessEncoderIntCall
  WriteSuccessEncoderOptionalU64Spec
  WriteSuccessEncoderU256Spec
  WriteSuccessEpilogueBlock
  WriteSuccessHeaderSpec
  WriteSuccessNativeSuffixBytes158e0
  WriteSuccessNativeSuffixIntPair
  WriteSuccessPrologueSpec
  WriteSuccessStorageKeysSpec
  WriteSuccessSuffixHashes15744Raw
  WriteSuccessTransactionsSpec
  WriteSuccessWithdrawalsSpec.

Definition writeSuccessPrologueBoundary `{!islaG Sigma} `{!threadG} :=
  @write_success_prologue_entry Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessPrologueBoundary) := I.

Definition writeSuccessHeaderBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessHeaderSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessHeaderBoundary) := I.

Definition writeSuccessTransactionsEntryBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessTransactionsLoopSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTransactionsEntryBoundary) := I.

Definition writeSuccessTransactionsExitBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessTransactionsLoopExit Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTransactionsExitBoundary) := I.

Definition writeSuccessAccessListsBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessAccessListsLoopSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessAccessListsBoundary) := I.

Definition writeSuccessStorageKeysBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessStorageKeysLoopSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessStorageKeysBoundary) := I.

Definition writeSuccessBlobHashesBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessBlobHashesLoopSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessBlobHashesBoundary) := I.

Definition writeSuccessAuthorizationsBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessAuthorizationsLoopSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessAuthorizationsBoundary) := I.

Definition writeSuccessPostTransactionsBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessTransactionsPostAt15668Spec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessPostTransactionsBoundary) := I.

Definition writeSuccessWithdrawalsBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessWithdrawalsLoopSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessWithdrawalsBoundary) := I.

Definition writeSuccessPostWithdrawalsBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixAt156e8 Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessPostWithdrawalsBoundary) := I.

Definition writeSuccessSuffixHashesBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixHashes15744Spec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessSuffixHashesBoundary) := I.

Definition writeSuccessTailBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixAt158e0 Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTailBoundary) := I.

Definition writeSuccessEpilogueBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessEpilogueSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessEpilogueBoundary) := I.

Definition writeOutputEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuWriteOutputCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeOutputEntryBoundary) := I.

Definition memcpyEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuMemcpyCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@memcpyEntryBoundary) := I.

Definition encoderBooleanEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBooleanCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderBooleanEntryBoundary) := I.

Definition encoderOptionalEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderOptionalU64CallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderOptionalEntryBoundary) := I.

Definition encoderByteListsEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderByteListsCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderByteListsEntryBoundary) := I.

Definition encoderBytesEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBytesCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderBytesEntryBoundary) := I.

Definition encoderU256EntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderU256CallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderU256EntryBoundary) := I.

Definition encoderIntEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderIntCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderIntEntryBoundary) := I.

(* Each call specification quantifies over RET and contains its exact return
   resources. These aliases expose that return interface without copying it. *)
Definition writeOutputReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuWriteOutputCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeOutputReturnBoundary) := I.

Definition memcpyReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuMemcpyCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@memcpyReturnBoundary) := I.

Definition encoderBooleanReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBooleanCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderBooleanReturnBoundary) := I.

Definition encoderOptionalReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderOptionalU64CallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderOptionalReturnBoundary) := I.

Definition encoderByteListsReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderByteListsCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderByteListsReturnBoundary) := I.

Definition encoderBytesReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBytesCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderBytesReturnBoundary) := I.

Definition encoderU256ReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderU256CallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderU256ReturnBoundary) := I.

Definition encoderIntReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderIntCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderIntReturnBoundary) := I.

Lemma write_success_interfaces_transactions_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsEntryBoundary P ⊣⊢
    writeSuccessTransactionsLoopSpec P.
Proof. done. Qed.

Lemma write_success_interfaces_output_return
    `{!islaG Sigma} `{!threadG} :
  writeOutputReturnBoundary ⊣⊢ zesuWriteOutputCallSpec.
Proof. done. Qed.

Print Assumptions write_success_interfaces_transactions_entry.
Print Assumptions write_success_interfaces_output_return.
