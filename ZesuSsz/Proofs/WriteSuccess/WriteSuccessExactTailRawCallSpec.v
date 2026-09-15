Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces
  WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessTransactionsSpec
  WriteSuccessExactTransactionsLiveSpec WriteSuccessExactValueSpec WriteSuccessValueBlock
  WriteSuccessByteLists WriteSuccessPostTransactionResources
  WriteSuccessPostTransactionDescriptors WriteSuccessObservation WriteSuccessExactTrace
  WriteSuccessOutputSemantic.
Open Scope Z_scope.
Definition exactTailAfterRawEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  writeOutputPayloadsSpec
    (writeSuccessAfterTransactionsDescriptors (writeSuccessFrameSp witness)
      (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness))
    (map writeSuccessPrivateBytes (writeSuccessWithdrawalListFragments observation ++
      writeSuccessPostFragments observation)) (writeSuccessTraceTail witness).
Definition exactTailRawCallMemoryFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (writeSuccessTransactionBase witness ↦ₘ∗
     WriteSuccessNativeContract.writeSuccessTransactionBytes witness ∗
   writeSuccessTransactionsOwn (writeSuccessTransactions witness) ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 (writeSuccessTransactionBase witness) ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (length (writeSuccessTransactions witness)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 160 ∗ (bv_unsigned sp + 1640) ↦ₘ? 256 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   writeSuccessExactValueMemory sp values ∗ (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactTailRawCallMemoryFrame) := I.

Definition exactTailRawCallFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   exactTailRawCallMemoryFrame args witness P)%I.
Global Instance : LithiumUnfold (@exactTailRawCallFrame) := I.

Definition exactTailRawLoadFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (writeSuccessTransactionBase witness ↦ₘ∗
     WriteSuccessNativeContract.writeSuccessTransactionBytes witness ∗
   writeSuccessTransactionsOwn (writeSuccessTransactions witness) ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 (writeSuccessTransactionBase witness) ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (length (writeSuccessTransactions witness)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 160 ∗ (bv_unsigned sp + 1640) ↦ₘ? 256 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗ writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactTailRawLoadFrame) := I.

Definition exactTailRawLoadMachineFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned (writeSuccessFrameSp witness) - 48) ↦ₘ? 48 ∗
   (bv_unsigned (writeSuccessFrameSp witness) - 80) ↦ₘ? 32 ∗
   byteListItemResources
     (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 9))
     (writeSuccessRawTransactions witness) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   exactTailRawLoadFrame args witness P)%I.
Global Instance : LithiumUnfold (@exactTailRawLoadMachineFrame) := I.
