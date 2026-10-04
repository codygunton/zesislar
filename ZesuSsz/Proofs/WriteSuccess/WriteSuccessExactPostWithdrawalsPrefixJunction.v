Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMemory.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessValueSpec WriteSuccessOutputSemantic
  WriteSuccessPostTransactionDescriptors WriteSuccessExactEncoderIntCall
  WriteSuccessExactPostWithdrawalsSplit.

(* Private proof-only junction draft. The public prefix contract is unchanged. *)
Definition writeSuccessPostWithdrawals156f4UntouchedRaw
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  let words := WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness) in
  (bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗
     writeSuccessWithdrawalsBytes witness ∗
   (bv_unsigned sp + 72) ↦ₘ WriteSuccessPostTransactionResources.writeSuccessPostWord words 7 ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x6"; "x7"; "x16"; "x17";
      "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
      "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
   (bv_unsigned sp - 80) ↦ₘ? 32 ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗ bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWordsWithout7 sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   (bv_unsigned sp + 1584) ↦ₘ∗ take 4 (drop 552 (bytes_of_u64s values)) ∗
   (bv_unsigned sp + 1588) ↦ₘ∗ WriteSuccessExactValueSpec.writeSuccessValueBlockHash values ∗
   (bv_unsigned sp + 1620) ↦ₘ∗ drop 588 (bytes_of_u64s values) ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   ByteLists.byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources sp
     (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
     (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗ P ∗ True)%I.

Lemma writeSuccessPostWithdrawals156f4UntouchedRaw_unfold
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) :
  writeSuccessPostWithdrawals156f4UntouchedRaw args witness P ⊣⊢
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  let words := WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness) in
  (bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗
     writeSuccessWithdrawalsBytes witness ∗
   (bv_unsigned sp + 72) ↦ₘ WriteSuccessPostTransactionResources.writeSuccessPostWord words 7 ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x6"; "x7"; "x16"; "x17";
      "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
      "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
   (bv_unsigned sp - 80) ↦ₘ? 32 ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗ bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWordsWithout7 sp (writeSuccessDecodedBytes witness) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ writeSuccessSourceBytes witness ∗
   (bv_unsigned sp + 1584) ↦ₘ∗ take 4 (drop 552 (bytes_of_u64s values)) ∗
   (bv_unsigned sp + 1588) ↦ₘ∗ WriteSuccessExactValueSpec.writeSuccessValueBlockHash values ∗
   (bv_unsigned sp + 1620) ↦ₘ∗ drop 588 (bytes_of_u64s values) ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   ByteLists.byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources sp
     (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
     (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) []
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗ P ∗ True)%I.
Proof. done. Qed.
Global Opaque writeSuccessPostWithdrawals156f4UntouchedRaw.

Definition writeSuccessPostWithdrawals156f4Untouched
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessPostWithdrawals156f4UntouchedRaw args witness P.

Lemma writeSuccessPostWithdrawals156f4Untouched_unfold
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) :
  writeSuccessPostWithdrawals156f4Untouched args witness P ⊣⊢
    writeSuccessPostWithdrawals156f4UntouchedRaw args witness P.
Proof. done. Qed.

Global Opaque writeSuccessPostWithdrawals156f4Untouched.

Definition writeSuccessPostWithdrawalsAt156f4
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (encoderIntExactReturn sp (BV 64 0x156f4) (exactPostWithdrawalsFirstTail witness) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x12"; "x13"; "x14"; "x15"]) ∗
   "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   "x8" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (bv_unsigned (writeSuccessWithdrawalsBase witness) +
       Z.of_nat (length (writeSuccessWithdrawalsBytes witness)))) ∗
   "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 69 (writeSuccessValues witness) ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   writeSuccessPostWithdrawals156f4Untouched args witness P ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessPostWithdrawalsAt156f4) := I.
