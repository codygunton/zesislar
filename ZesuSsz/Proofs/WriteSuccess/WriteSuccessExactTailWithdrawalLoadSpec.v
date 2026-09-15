Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostTransactionsWithdrawalLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Open Scope Z_scope.

Definition exactTailWithdrawalLoadCallerShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
  ["x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x5"; "x6"; "x7"; "x28"; "x29"; "x30"; "x31"].

Definition exactTailWithdrawalLoadSavedShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
  ["x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"].

Definition exactTailWithdrawalValueRemainder `{!islaG Sigma}
    (sp : bv 64) (values : list (bv 64)) : iProp Sigma :=
  ((bv_unsigned sp + 1584) ↦ₘ∗ take 4 (drop 552 (bytes_of_u64s values)) ∗
   (bv_unsigned sp + 1588) ↦ₘ∗ writeSuccessValueBlockHash values ∗
   (bv_unsigned sp + 1620) ↦ₘ∗ drop 588 (bytes_of_u64s values))%I.
Global Instance : LithiumUnfold (@exactTailWithdrawalValueRemainder) := I.

Definition exactTailWithdrawalLoadFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (reg_col exactTailWithdrawalLoadCallerShapes ∗
   reg_col exactTailWithdrawalLoadSavedShapes ∗
   reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   reg_col [(KindReg "x11", BitsShape 64)] ∗
   (bv_unsigned sp - 80) ↦ₘ? 80 ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (exactTailAfterRawEvents witness) ∗
   exactTailWithdrawalValueRemainder sp values ∗
   writeSuccessTransactionBase witness ↦ₘ∗
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
Global Instance : LithiumUnfold (@exactTailWithdrawalLoadFrame) := I.

Definition exactTailWithdrawalLoadEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ oldra old8 old9 olddata : bv 64,
    postTransactionsWithdrawalLoadEntry (writeSuccessFrameSp witness)
      oldra old8 old9 olddata (take 69 (writeSuccessValues witness))
      (exactTailWithdrawalLoadFrame args witness P))%I.
Global Instance : LithiumUnfold (@exactTailWithdrawalLoadEntry) := I.

Definition exactTailWithdrawalLoadPost `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  postTransactionsWithdrawalLoadPost (writeSuccessFrameSp witness)
    (take 69 (writeSuccessValues witness))
    (exactTailWithdrawalLoadFrame args witness P).
Global Instance : LithiumUnfold (@exactTailWithdrawalLoadPost) := I.
