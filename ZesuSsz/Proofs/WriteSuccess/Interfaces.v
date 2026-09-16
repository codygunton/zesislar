Require Import ZesuSsz.Automation.AllLegacy.
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
  WriteSuccessExactTransactionsLiveSpec
  WriteSuccessAccessListsSpec
  WriteSuccessAuthorizationsSpec
  WriteSuccessBlobHashesSpec
  WriteSuccessByteLists
  WriteSuccessCalls
  WriteSuccessExactBooleanClosedCall
  WriteSuccessExactByteListsClosedCall
  WriteSuccessExactEncoderBytes
  WriteSuccessExactEncoderOptionalU64Call
  WriteSuccessExactTailRawLoadSpec
  WriteSuccessExactWithdrawalsLoopSpec
  WriteSuccessExactWriteOutputCall
  WriteSuccessEncoderBooleanCall
  WriteSuccessEncoderBytesCallCore
  WriteSuccessEncoderIntCall
  WriteSuccessEncoderOptionalU64Spec
  WriteSuccessEncoderU256Spec
  WriteSuccessEpilogueBlock
  WriteSuccessHeaderSpec
  WriteSuccessNativeSuffixBytes158e0
  WriteSuccessNativeSuffixConditionalBranch
  WriteSuccessNativeSuffixInt15968Call
  WriteSuccessNativeSuffixOptionalU64159b8
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

(** Exact transaction boundaries retain the caller's live stack resources. *)
Definition writeSuccessExactTransactionsEntryBoundary
    `{!islaG Sigma} `{!threadG} :=
  @transactionLiveLoopState Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessExactTransactionsEntryBoundary) := I.

Definition writeSuccessExactTransactionsExitBoundary
    `{!islaG Sigma} `{!threadG} :=
  @transactionLiveLoopExit Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessExactTransactionsExitBoundary) := I.

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

Definition writeSuccessExactPostTransactionsBoundary
    `{!islaG Sigma} `{!threadG} := @exactTailRawLoadEntry Sigma _ _.
Global Instance : LithiumUnfold
  (@writeSuccessExactPostTransactionsBoundary) := I.

Definition writeSuccessWithdrawalsBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessWithdrawalsLoopSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessWithdrawalsBoundary) := I.

Definition writeSuccessPostWithdrawalsBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixAt156e8 Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessPostWithdrawalsBoundary) := I.

Definition writeSuccessExactPostWithdrawalsBoundary
    `{!islaG Sigma} `{!threadG} := @withdrawalLoopExit Sigma _ _.
Global Instance : LithiumUnfold
  (@writeSuccessExactPostWithdrawalsBoundary) := I.

Definition writeSuccessSuffixHashesBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixHashes15744Spec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessSuffixHashesBoundary) := I.

Definition writeSuccessTailBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixAt158e0 Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTailBoundary) := I.

Definition writeSuccessTailFieldsEntryBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixAt158e0 Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTailFieldsEntryBoundary) := I.

Definition writeSuccessTailFirstBranchBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffix1596cLoadSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTailFirstBranchBoundary) := I.

Definition writeSuccessTailSecondBranchBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessSuffixOptionalU64159b8Spec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTailSecondBranchBoundary) := I.

Definition writeSuccessTailFieldsExitBoundary
    `{!islaG Sigma} `{!threadG} :=
  @writeSuccessEpilogueSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessTailFieldsExitBoundary) := I.

Definition writeSuccessEpilogueBoundary `{!islaG Sigma} `{!threadG} :=
  @writeSuccessEpilogueSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeSuccessEpilogueBoundary) := I.

Definition writeSuccessExactEpilogueAddSpSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64),
    reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessOtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits s0 ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
    "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
    "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
    "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
    "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
    "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
    writeSuccessEpilogueSavedSlots
      sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp + 1896⌝ ∗
    ⌜bv_unsigned sp + 2000 < machineRamEnd defaultMap⌝ ∗
    ⌜bv_extract 0 1 ra = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ra = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ra = BV 2 0⌝ ∗ P ∗
    instr_pre
      (bv_unsigned
        (bv_or (bv_and (ra + 0)%bv (BV 64 18446744073709551614))
          (BV 64 0)))
      (writeSuccessEpiloguePost
        sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P) ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactEpilogueAddSpSpec) := I.

Definition writeOutputEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @writeOutputExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeOutputEntryBoundary) := I.

Definition memcpyEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuMemcpyCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@memcpyEntryBoundary) := I.

Definition encoderBooleanEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBooleanExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderBooleanEntryBoundary) := I.

Definition encoderOptionalEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderOptionalU64ExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderOptionalEntryBoundary) := I.

Definition encoderByteListsEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderByteListsExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderByteListsEntryBoundary) := I.

Definition encoderBytesEntryBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBytesExactCallSpec Sigma _ _.
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
  @writeOutputExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@writeOutputReturnBoundary) := I.

Definition memcpyReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuMemcpyCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@memcpyReturnBoundary) := I.

Definition encoderBooleanReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBooleanExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderBooleanReturnBoundary) := I.

Definition encoderOptionalReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderOptionalU64ExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderOptionalReturnBoundary) := I.

Definition encoderByteListsReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderByteListsExactCallSpec Sigma _ _.
Global Instance : LithiumUnfold (@encoderByteListsReturnBoundary) := I.

Definition encoderBytesReturnBoundary `{!islaG Sigma} `{!threadG} :=
  @zesuEncoderBytesExactCallSpec Sigma _ _.
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
  writeOutputReturnBoundary ⊣⊢ writeOutputExactCallSpec.
Proof. done. Qed.

Print Assumptions write_success_interfaces_transactions_entry.
Print Assumptions write_success_interfaces_output_return.

(** Exact caller frame shared by the transactions and terminal chains. *)
Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessExactValueSpec WriteSuccessValueBlock
  WriteSuccessByteLists WriteSuccessTransactionsSpec
  WriteSuccessTransactionsPost15674Boundary
  WriteSuccessPostTransactionResources.

Definition writeSuccessExitMemoryFrame `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  writeSuccessNativeExitMemory witness.
Global Instance : LithiumUnfold (@writeSuccessExitMemoryFrame) := I.

Definition writeSuccessExactEpilogueExit `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  (writeSuccessExitMemoryFrame witness ∗
   spec_trace (writeSuccessTraceTail witness))%I.

Lemma writeSuccessExactEpilogueExit_unfold `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessExactEpilogueExit witness ⊣⊢
    (writeSuccessExitMemoryFrame witness ∗
     spec_trace (writeSuccessTraceTail witness))%I.
Proof. done. Qed.

Global Opaque writeSuccessExactEpilogueExit.
Global Instance : LithiumUnfold (@writeSuccessExactEpilogueExit) := I.

Definition writeSuccessExactCallerRemainder `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactCallerRemainder) := I.

Definition writeSuccessExactTailCaller `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   bv_unsigned sp ↦ₘ? 104 ∗ (bv_unsigned sp + 280) ↦ₘ? 32 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactTailCaller) := I.

(** The load chain copies decoded bytes 720..847 into persistent stack words.
    The suffix reads these words. The legacy free-stack adapter stays unchanged. *)
Definition writeSuccessExactCopiedTailWords `{!islaG Sigma}
    (sp : bv 64) (decodedBytes : list (bv 8)) : iProp Sigma :=
  let words := writeSuccessPostTailWords decodedBytes in
  ((bv_unsigned sp + 24) ↦ₘ writeSuccessPostWord words 0 ∗
   (bv_unsigned sp + 16) ↦ₘ writeSuccessPostWord words 1 ∗
   (bv_unsigned sp + 40) ↦ₘ writeSuccessPostWord words 2 ∗
   (bv_unsigned sp + 32) ↦ₘ writeSuccessPostWord words 3 ∗
   (bv_unsigned sp + 56) ↦ₘ writeSuccessPostWord words 4 ∗
   (bv_unsigned sp + 48) ↦ₘ writeSuccessPostWord words 5 ∗
   (bv_unsigned sp + 64) ↦ₘ writeSuccessPostWord words 6 ∗
   (bv_unsigned sp + 72) ↦ₘ writeSuccessPostWord words 7 ∗
   (bv_unsigned sp + 8) ↦ₘ writeSuccessPostWord words 8 ∗
   (bv_unsigned sp + 80) ↦ₘ writeSuccessPostWord words 9 ∗
   (bv_unsigned sp + 296) ↦ₘ writeSuccessPostWord words 10 ∗
   (bv_unsigned sp + 304) ↦ₘ writeSuccessPostWord words 11 ∗
   (bv_unsigned sp + 280) ↦ₘ writeSuccessPostWord words 12 ∗
   (bv_unsigned sp + 288) ↦ₘ writeSuccessPostWord words 13 ∗
   (bv_unsigned sp + 96) ↦ₘ writeSuccessPostWord words 14 ∗
   (bv_unsigned sp + 88) ↦ₘ writeSuccessPostWord words 15)%I.
Global Instance : LithiumUnfold (@writeSuccessExactCopiedTailWords) := I.

Definition writeSuccessExactTailCallerWithCopiedWords `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactTailCallerWithCopiedWords) := I.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTrace.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Definition writeSuccessExactTailEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  let sp := writeSuccessFrameSp witness in
  writeOutputPayloadsSpec
    (writeSuccessByteListsDescriptors sp (writeSuccessRawTransactions witness) ++
     writeSuccessAfterTransactionsDescriptors sp (writeSuccessWithdrawalsCount witness)
       (writeSuccessPostData witness))
    (drop (length (writeSuccessMainDescriptors sp (writeSuccessValues witness)
       (writeSuccessTransactions witness)))
      (writeSuccessExactPayloads (writeSuccessDecodedBytes witness)
        (writeSuccessValues witness) (writeSuccessPayload witness)
        (writeSuccessTransactions witness) (writeSuccessRawTransactions witness)
        (writeSuccessWithdrawalsBytes witness) (writeSuccessWithdrawalsCount witness)
        (writeSuccessPostData witness)))
    (writeSuccessTraceTail witness).

Definition writeSuccessExactPostWithdrawalsPayloads {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : list (list (bv 8)) :=
  drop
    (length (writeSuccessMainDescriptors
      (writeSuccessFrameSp witness) (writeSuccessValues witness)
      (writeSuccessTransactions witness)) +
     length (writeSuccessByteListsDescriptors
      (writeSuccessFrameSp witness) (writeSuccessRawTransactions witness)) +
     length (writeSuccessWithdrawalsDescriptors
      (writeSuccessFrameSp witness) (writeSuccessWithdrawalsCount witness)))
    (writeSuccessExactPayloads (writeSuccessDecodedBytes witness)
      (writeSuccessValues witness) (writeSuccessPayload witness)
      (writeSuccessTransactions witness) (writeSuccessRawTransactions witness)
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness)).

Definition writeSuccessExactPostWithdrawalsEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  writeOutputPayloadsSpec
    (writeSuccessPost156e8Descriptors
      (writeSuccessFrameSp witness) (writeSuccessPostData witness))
    (writeSuccessExactPostWithdrawalsPayloads witness)
    (writeSuccessTraceTail witness).

Definition writeSuccessExactPostWithdrawalsMemoryFrame
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
     writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗
     writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   writeSuccessPostTransactionDataResources sp
     (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
     (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.
Global Instance : LithiumUnfold
  (@writeSuccessExactPostWithdrawalsMemoryFrame) := I.

Definition writeSuccessExactPostWithdrawalsCallerFrame
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x3"; "x4"; "x6"; "x7"; "x16"; "x17";
       "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
       "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   writeSuccessExactPostWithdrawalsMemoryFrame args witness)%I.
Global Instance : LithiumUnfold
  (@writeSuccessExactPostWithdrawalsCallerFrame) := I.

Definition writeSuccessExactTailFirstBranchState
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (tail : spec) : iProp Sigma :=
  (∃ b8 b9 b12 b13 b14 b15 b18 : bv 64,
    writeSuccessSuffixInt1596cCallPost (writeSuccessFrameSp witness) tail ∗
    "x8" ↦ᵣ RVal_Bits b8 ∗ "x9" ↦ᵣ RVal_Bits b9 ∗
    "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
    "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
    "x18" ↦ᵣ RVal_Bits b18 ∗
    writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ True)%I.
Global Instance : LithiumUnfold
  (@writeSuccessExactTailFirstBranchState) := I.

Definition writeSuccessExactTailSecondBranchState
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  writeSuccessSuffixOptionalU64159b8Spec
    (reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
     writeSuccessExactPostWithdrawalsMemoryFrame args witness ∗ True).
Global Instance : LithiumUnfold
  (@writeSuccessExactTailSecondBranchState) := I.
