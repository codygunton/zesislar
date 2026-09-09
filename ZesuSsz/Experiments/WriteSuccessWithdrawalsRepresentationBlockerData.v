From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessParserLemmas.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessBlockerOwner : Z := 0x20002000.
Definition writeSuccessBlockerScratch : Z := 0x200016d0.
Definition writeSuccessBlockerCurrent : list (bv 8) :=
  Z_to_bv 8 1 :: repeat (Z_to_bv 8 0) 47.

Lemma writeSuccessBlockerCurrentLength :
  length writeSuccessBlockerCurrent = 48%nat.
Proof. reflexivity. Qed.
Definition writeSuccessBlockerWithdrawal : WriteSuccessWithdrawalObservation := {|
  observationWithdrawalIndex := 1;
  observationWithdrawalValidatorIndex := 0;
  observationWithdrawalAddress := repeat 0 20;
  observationWithdrawalAmount := 0
|}.

Definition writeSuccessBlockerNextWithdrawal :
    WriteSuccessWithdrawalObservation := {|
  observationWithdrawalIndex := 0;
  observationWithdrawalValidatorIndex := 0;
  observationWithdrawalAddress := repeat 0 20;
  observationWithdrawalAmount := 0
|}.

Definition writeSuccessBlockerNext : list (bv 8) :=
  repeat (Z_to_bv 8 0) 48.

Definition writeSuccessBlockerAllBytes : list (bv 8) :=
  writeSuccessBlockerCurrent ++ writeSuccessBlockerNext.

Definition writeSuccessBlockerDecoded : WriteSuccessObservation := {|
  observationParentHash := repeat 0 32;
  observationFeeRecipient := repeat 0 20;
  observationStateRoot := repeat 0 32;
  observationReceiptsRoot := repeat 0 32;
  observationLogsBloom := repeat 0 256;
  observationPrevRandao := repeat 0 32;
  observationBlockNumber := 0;
  observationGasLimit := 0;
  observationGasUsed := 0;
  observationTimestamp := 0;
  observationExtraData := [0];
  observationBaseFee := 0;
  observationBlockHash := repeat 0 32;
  observationTransactions := [];
  observationRawTransactions := [];
  observationWithdrawals :=
    [writeSuccessBlockerWithdrawal; writeSuccessBlockerNextWithdrawal];
  observationBlobGasUsed := 0;
  observationExcessBlobGas := 0;
  observationSlotNumber := None;
  observationBlockAccessList := [];
  observationParentBeaconRoot := repeat 0 32;
  observationVersionedHashes := [];
  observationDeposits := [];
  observationWithdrawalRequests := [];
  observationConsolidations := [];
  observationBuilderDeposits := [];
  observationBuilderExits := [];
  observationWitnessNodes := [];
  observationWitnessCodes := [];
  observationWitnessHeaders := [];
  observationChainId := 0;
  observationForkName := None;
  observationActiveForkIndex := 0;
  observationActivationBlock := None;
  observationActivationTimestamp := None;
  observationPublicKeys := []
|}.

Definition writeSuccessBlockerZeroMemory : mem_map :=
  write_mem_list
    (write_mem_list
      (write_mem_list
        (write_mem_list (∅ : mem_map) (Z_to_bv 64 writeSuccessBlockerOwner)
          (repeat (Z_to_bv 8 0) 848))
        (Z_to_bv 64 0x20001000) (repeat (Z_to_bv 8 0) 96))
      (Z_to_bv 64 0x20000ff0) (repeat (Z_to_bv 8 0) 16))
    (Z_to_bv 64 writeSuccessBlockerScratch) (repeat (Z_to_bv 8 0) 48).

Definition writeSuccessBlockerIntegerBytes (value : Z) : list (bv 8) :=
  map (Z_to_bv 8) (writeSuccessLayoutLe 8 value).

Definition writeSuccessBlockerMemory : mem_map :=
  write_mem_list
    (write_mem_list
      (write_mem_list
        (write_mem_list writeSuccessBlockerZeroMemory
          (Z_to_bv 64 (writeSuccessBlockerOwner + 32))
          (writeSuccessBlockerIntegerBytes writeSuccessBlockerScratch))
        (Z_to_bv 64 (writeSuccessBlockerOwner + 40))
        (writeSuccessBlockerIntegerBytes 1))
      (Z_to_bv 64 (writeSuccessBlockerOwner + 88))
      (writeSuccessBlockerIntegerBytes 0x20001000))
    (Z_to_bv 64 (writeSuccessBlockerOwner + 96))
    (writeSuccessBlockerIntegerBytes 2).

Definition writeSuccessBlockerRepresentedMemory : mem_map :=
  write_mem_list writeSuccessBlockerMemory (Z_to_bv 64 0x20001000)
    writeSuccessBlockerAllBytes.

Lemma writeSuccessBlockerDecodedValid :
  writeSuccessObservationValid writeSuccessBlockerDecoded.
Proof.
  unfold writeSuccessBlockerDecoded, writeSuccessBlockerWithdrawal,
    writeSuccessBlockerNextWithdrawal,
    writeSuccessObservationValid, writeSuccessWithdrawalObservationValid,
    writeSuccessBytesValid, writeSuccessVariableBytesValid,
    writeSuccessListValid, writeSuccessLengthValid,
    writeSuccessUnsignedValid, writeSuccessOptionValid.
  cbn. repeat split; try lia.
  all: repeat constructor; cbn; lia.
Qed.


Print Assumptions writeSuccessBlockerCurrentLength.
Print Assumptions writeSuccessBlockerDecodedValid.
