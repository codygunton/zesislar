From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessRamCounterexampleZero : bv 64 := BV 64 0.
Definition writeSuccessRamCounterexampleBase : bv 64 := BV 64 0x20000000.

Definition writeSuccessRamCounterexampleValues : list (bv 64) :=
  repeat writeSuccessRamCounterexampleZero 9 ++
  [writeSuccessRamCounterexampleBase; writeSuccessRamCounterexampleZero;
   writeSuccessRamCounterexampleBase; writeSuccessRamCounterexampleZero] ++
  repeat writeSuccessRamCounterexampleZero 61.

Definition writeSuccessRamCounterexampleSource : list (bv 8) :=
  bytes_of_u64s writeSuccessRamCounterexampleValues ++
  repeat (BV 8 0) 128.

Definition writeSuccessRamCounterexampleDecoded : list (bv 8) :=
  writeSuccessRamCounterexampleSource ++ repeat (BV 8 0) 128.

Definition writeSuccessRamCounterexamplePostData :
    WriteSuccessPostTransactionData := {|
  writeSuccessPostOptional15700 := None;
  writeSuccessPostBytes1571c :=
    (writeSuccessRamCounterexampleZero, writeSuccessRamCounterexampleZero);
  writeSuccessPostHashesCount := 0;
  writeSuccessPostBytes158e0 :=
    (writeSuccessRamCounterexampleZero, writeSuccessRamCounterexampleZero);
  writeSuccessPostBytes158f0 :=
    (writeSuccessRamCounterexampleZero, writeSuccessRamCounterexampleZero);
  writeSuccessPostBytes15900 :=
    (writeSuccessRamCounterexampleZero, writeSuccessRamCounterexampleZero);
  writeSuccessPostBytes15910 :=
    (writeSuccessRamCounterexampleZero, writeSuccessRamCounterexampleZero);
  writeSuccessPostBytes15920 :=
    (writeSuccessRamCounterexampleZero, writeSuccessRamCounterexampleZero);
  writeSuccessPostByteLists15930 := [];
  writeSuccessPostByteLists15940 := [];
  writeSuccessPostByteLists15950 := [];
  writeSuccessPostConditional1596c := None;
  writeSuccessPostOptional159b0 := None;
  writeSuccessPostOptional159bc := None;
  writeSuccessPostByteLists159c8 := []
|}.

Definition writeSuccessRamCounterexampleWitness :
    writeSuccessNativeWitness unit := {|
  writeSuccessEntrySp := BV 64 0x20001000;
  writeSuccessDecodedPointer := BV 64 0x20001020;
  writeSuccessReturnValue := BV 64 0x14d10;
  writeSuccessSavedS0 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS1 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS2 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS3 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS4 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS5 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS6 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS7 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS8 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS9 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS10 := writeSuccessRamCounterexampleZero;
  writeSuccessSavedS11 := writeSuccessRamCounterexampleZero;
  writeSuccessDecodedBytes := writeSuccessRamCounterexampleDecoded;
  writeSuccessSourceBytes := writeSuccessRamCounterexampleSource;
  writeSuccessValues := writeSuccessRamCounterexampleValues;
  writeSuccessPayload := [];
  writeSuccessTraceTail := fun _ => True;
  writeSuccessTransactionBase := 0;
  writeSuccessTransactions := [];
  writeSuccessTransactionBytes := [];
  writeSuccessRawTransactions := [];
  writeSuccessWithdrawalsBase := writeSuccessRamCounterexampleBase;
  writeSuccessWithdrawalsBytes := [];
  writeSuccessWithdrawalsCount := 0;
  writeSuccessPostData := writeSuccessRamCounterexamplePostData
|}.

Definition writeSuccessRamCounterexampleArgs : WriteSuccessArgs unit := {|
  successReturnAddress := 0x14d10;
  successStackPointer := 0x20001000;
  successDecodedAddress := 0x20001020;
  successDecoded := tt;
  successInputSize := 0
|}.

Lemma writeSuccessAcceptedWitnessAllowsTransactionBaseOutsideRam :
  writeSuccessWitnessWellFormed writeSuccessRamCounterexampleArgs
    writeSuccessRamCounterexampleWitness /\
  writeSuccessTransactionBase writeSuccessRamCounterexampleWitness = 0 /\
  ~ (0x20000000 <=
       writeSuccessTransactionBase writeSuccessRamCounterexampleWitness /\
     writeSuccessTransactionBase writeSuccessRamCounterexampleWitness +
       Z.of_nat (length (writeSuccessTransactionBytes
         writeSuccessRamCounterexampleWitness)) < 0x40000000).
Proof.
  vm_compute. repeat split; try lia; try reflexivity.
  all: try congruence; try done.
  all: try (apply bv_eq; reflexivity).
  intros [Hminimum _]. exact (Hminimum eq_refl).
Qed.

Print Assumptions writeSuccessAcceptedWitnessAllowsTransactionBaseOutsideRam.
