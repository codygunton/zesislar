(* Native successor capture; no resources added. *)
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.

Definition NativeRootState_14d30
    `{!islaG Sigma} `{!threadG} {Decoded : Type} `{!WriteSuccessMemoryRepresentation Decoded} (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  (∃ v : valu,
   ∃ v0 : valu,
   ∃ v1 : bv 64,
   ∃ v2 : bv 64,
   ∃ v3 : bv 64,
   ∃ v4 : bv 64,
   ∃ v5 : bv 64,
   ∃ v6 : bv 64,
   ∃ v7 : bv 64,
   ∃ v8 : bv 64,
   ∃ v9 : bv 64,
   ∃ v10 : bv 64,
   ∃ v11 : bv 64,
   ∃ v12 : bv 64,
   ∃ v13 : bv 64,
   ∃ vact : valu,
   ∃ vact0 : valu,
   ∃ vact1 : valu,
   ∃ vact2 : valu,
   ∃ vact3 : valu,
   ∃ vact4 : valu,
   ∃ vact5 : valu,
   ∃ vact6 : valu,
   ∃ vact7 : valu,
   ∃ vact8 : valu,
   ∃ vact9 : valu,
   ∃ vact10 : valu,
   ∃ vact11 : valu,
   ∃ vact12 : valu,
   (reg_col zesu_ram_sys_regs) ∗
   (⌜valu_has_shape vact (BitsShape 64)⌝) ∗
   ("x3" ↦ᵣ vact) ∗
   (⌜valu_has_shape vact0 (BitsShape 64)⌝) ∗
   ("x4" ↦ᵣ vact0) ∗
   (⌜valu_has_shape vact1 (BitsShape 64)⌝) ∗
   ("x5" ↦ᵣ vact1) ∗
   (⌜valu_has_shape vact2 (BitsShape 64)⌝) ∗
   ("x6" ↦ᵣ vact2) ∗
   (⌜valu_has_shape vact3 (BitsShape 64)⌝) ∗
   ("x7" ↦ᵣ vact3) ∗
   (⌜valu_has_shape vact4 (BitsShape 64)⌝) ∗
   ("x13" ↦ᵣ vact4) ∗
   (⌜valu_has_shape vact5 (BitsShape 64)⌝) ∗
   ("x14" ↦ᵣ vact5) ∗
   (⌜valu_has_shape vact6 (BitsShape 64)⌝) ∗
   ("x15" ↦ᵣ vact6) ∗
   (⌜valu_has_shape vact7 (BitsShape 64)⌝) ∗
   ("x16" ↦ᵣ vact7) ∗
   (⌜valu_has_shape vact8 (BitsShape 64)⌝) ∗
   ("x17" ↦ᵣ vact8) ∗
   (⌜valu_has_shape vact9 (BitsShape 64)⌝) ∗
   ("x28" ↦ᵣ vact9) ∗
   (⌜valu_has_shape vact10 (BitsShape 64)⌝) ∗
   ("x29" ↦ᵣ vact10) ∗
   (⌜valu_has_shape vact11 (BitsShape 64)⌝) ∗
   ("x30" ↦ᵣ vact11) ∗
   (⌜valu_has_shape vact12 (BitsShape 64)⌝) ∗
   ("x31" ↦ᵣ vact12) ∗
   (emp) ∗
   ("x1" ↦ᵣ RVal_Bits (writeSuccessReturnValue witness)) ∗
   ("x2" ↦ᵣ RVal_Bits (writeSuccessEntrySp witness)) ∗
   ("x8" ↦ᵣ RVal_Bits (writeSuccessSavedS0 witness)) ∗
   ("x9" ↦ᵣ RVal_Bits (writeSuccessSavedS1 witness)) ∗
   ("x18" ↦ᵣ RVal_Bits (writeSuccessSavedS2 witness)) ∗
   ("x19" ↦ᵣ RVal_Bits (writeSuccessSavedS3 witness)) ∗
   ("x20" ↦ᵣ RVal_Bits (writeSuccessSavedS4 witness)) ∗
   ("x21" ↦ᵣ RVal_Bits (writeSuccessSavedS5 witness)) ∗
   ("x22" ↦ᵣ RVal_Bits (writeSuccessSavedS6 witness)) ∗
   ("x23" ↦ᵣ RVal_Bits (writeSuccessSavedS7 witness)) ∗
   ("x24" ↦ᵣ RVal_Bits (writeSuccessSavedS8 witness)) ∗
   ("x25" ↦ᵣ RVal_Bits (writeSuccessSavedS9 witness)) ∗
   ("x26" ↦ᵣ RVal_Bits (writeSuccessSavedS10 witness)) ∗
   ("x27" ↦ᵣ RVal_Bits (writeSuccessSavedS11 witness)) ∗
   ("x10" ↦ᵣ RVal_Bits (writeSuccessDecodedPointer witness)) ∗
   ("x11" ↦ᵣ v) ∗
   ("x12" ↦ᵣ v0) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 104) ↦ₘ v1) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 96) ↦ₘ v2) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 88) ↦ₘ v3) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 80) ↦ₘ v4) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 72) ↦ₘ v5) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 64) ↦ₘ v6) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 56) ↦ₘ v7) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 48) ↦ₘ v8) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 40) ↦ₘ v9) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 32) ↦ₘ v10) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 24) ↦ₘ v11) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 16) ↦ₘ v12) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 8) ↦ₘ v13) ∗
   ((bv_unsigned (writeSuccessEntrySp witness) - 2000) ↦ₘ? 1896) ∗
   (bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness) ∗
   (mmio_range (machineOutputAddress defaultMap) 16) ∗
   (spec_trace (writeSuccessNativeTailEvents witness)) ∗
   ((bv_unsigned (writeSuccessFrameSp witness) - 48) ↦ₘ? 48) ∗
   ((bv_unsigned (writeSuccessFrameSp witness) - 80) ↦ₘ? 32) ∗
   (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 4) ↦ₘ∗ writeSuccessPayload witness) ∗
   (writeSuccessTransactionBase witness ↦ₘ∗ WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   (writeSuccessTransactionsOwn (writeSuccessTransactions witness)) ∗
   (writeSuccessTransactionsInvariant (writeSuccessFrameSp witness) (writeSuccessTransactionBase witness) (writeSuccessTransactions witness) [] (writeSuccessTransactions witness) (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)) ∗
   (⌜length (writeSuccessSourceBytes witness) = 720%nat⌝) ∗
   (⌜IslarisMemory.bytes_of_u64s (writeSuccessValues witness) = take 592 (writeSuccessSourceBytes witness)⌝) ∗
   (⌜length (writeSuccessValues witness) = 74%nat⌝) ∗
   (⌜bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 5) = length (writeSuccessPayload witness)⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 7 = Z_to_bv 64 (writeSuccessTransactionBase witness)⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 8 = Z_to_bv 64 (length (writeSuccessTransactions witness))⌝) ∗
   (⌜(bv_unsigned (writeSuccessFrameSp witness) `mod` 16)%Z = 0%Z⌝) ∗
   (⌜(bv_unsigned (writeSuccessFrameSp witness) `mod` 8)%Z = 0%Z⌝) ∗
   (⌜(mapRamBase defaultMap ≤ bv_unsigned (writeSuccessFrameSp witness) - 48)%Z⌝) ∗
   (⌜(bv_unsigned (writeSuccessFrameSp witness) + 1896 < machineRamEnd defaultMap)%Z⌝) ∗
   (True) ∗
   (byteListItemResources (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 9)) (writeSuccessRawTransactions witness)) ∗
   (bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness) ∗
   (⌜WriteSuccessTransactionsPost15674Boundary.writeSuccessTransactionsPost15674ByteListFacts (writeSuccessFrameSp witness) (writeSuccessValueWord (writeSuccessValues witness) 9) (writeSuccessValueWord (writeSuccessValues witness) 10) (writeSuccessRawTransactions witness)⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 11 = writeSuccessWithdrawalsBase witness⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 12 = Z_to_bv 64 (writeSuccessWithdrawalsCount witness)⌝) ∗
   (⌜length (writeSuccessWithdrawalsBytes witness) = (48 * writeSuccessWithdrawalsCount witness)%nat⌝) ∗
   (⌜(mapRamBase defaultMap ≤ bv_unsigned (writeSuccessWithdrawalsBase witness))%Z⌝) ∗
   (⌜(bv_unsigned (writeSuccessWithdrawalsBase witness) + length (writeSuccessWithdrawalsBytes witness) < machineRamEnd defaultMap)%Z⌝) ∗
   (writeSuccessPostTransactionDataResources (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness) (writeSuccessPostData witness)) ∗
   (writeSuccessNativeStaticResources) ∗
   (⌜length (writeSuccessDecodedBytes witness) = 848%nat⌝) ∗
   (⌜(mapRamBase defaultMap ≤ bv_unsigned (writeSuccessDecodedPointer witness))%Z⌝) ∗
   (⌜(bv_unsigned (writeSuccessDecodedPointer witness) + 848 < machineRamEnd defaultMap)%Z⌝) ∗
   (True) ∗
   (⌜successStackPointer Decoded args = bv_unsigned (writeSuccessEntrySp witness)⌝) ∗
   (⌜successDecodedAddress Decoded args = bv_unsigned (writeSuccessDecodedPointer witness)⌝) ∗
   (⌜successReturnAddress Decoded args = 85264%Z⌝) ∗
   (⌜writeSuccessReturnValue witness = Z_to_bv 64 (successReturnAddress Decoded args)⌝) ∗
   (⌜bv_unsigned (writeSuccessDecodedPointer witness) = (bv_unsigned (writeSuccessEntrySp witness) + 32)%Z⌝) ∗
   (⌜length (writeSuccessDecodedBytes witness) = 848%nat⌝) ∗
   (⌜length (writeSuccessSourceBytes witness) = 720%nat⌝) ∗
   (⌜writeSuccessSourceBytes witness = take 720 (writeSuccessDecodedBytes witness)⌝) ∗
   (⌜length (writeSuccessValues witness) = 74%nat⌝) ∗
   (⌜IslarisMemory.bytes_of_u64s (writeSuccessValues witness) = take 592 (writeSuccessSourceBytes witness)⌝) ∗
   (⌜bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 5) = length (writeSuccessPayload witness)⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 7 = Z_to_bv 64 (writeSuccessTransactionBase witness)⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 8 = Z_to_bv 64 (length (writeSuccessTransactions witness))⌝) ∗
   (⌜WriteSuccessNativeContract.writeSuccessTransactionBytes witness = writeSuccessTransactionsBytes (writeSuccessTransactions witness)⌝) ∗
   (⌜writeSuccessMemoryRepresents (writeSuccessDecodedBytes witness) (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessTransactions witness) (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness) (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) (successDecoded Decoded args)⌝) ∗
   (⌜WriteSuccessTransactionsPost15674Boundary.writeSuccessTransactionsPost15674ByteListFacts (writeSuccessFrameSp witness) (writeSuccessValueWord (writeSuccessValues witness) 9) (writeSuccessValueWord (writeSuccessValues witness) 10) (writeSuccessRawTransactions witness)⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 11 = writeSuccessWithdrawalsBase witness⌝) ∗
   (⌜writeSuccessValueWord (writeSuccessValues witness) 12 = Z_to_bv 64 (writeSuccessWithdrawalsCount witness)⌝) ∗
   (⌜length (writeSuccessWithdrawalsBytes witness) = (48 * writeSuccessWithdrawalsCount witness)%nat⌝) ∗
   (⌜(mapRamBase defaultMap ≤ bv_unsigned (writeSuccessWithdrawalsBase witness))%Z⌝) ∗
   (⌜(bv_unsigned (writeSuccessWithdrawalsBase witness) + length (writeSuccessWithdrawalsBytes witness) < machineRamEnd defaultMap)%Z⌝) ∗
   (⌜(bv_unsigned (writeSuccessEntrySp witness) `mod` 16)%Z = 0%Z⌝) ∗
   (⌜(mapRamBase defaultMap + 2176 ≤ bv_unsigned (writeSuccessEntrySp witness))%Z⌝) ∗
   (⌜(bv_unsigned (writeSuccessEntrySp witness) + 2000 < machineRamEnd defaultMap)%Z⌝) ∗
   (⌜bv_extract 0 4 (writeSuccessEntrySp witness) = 0%bv⌝) ∗
   (⌜(bv_unsigned (writeSuccessEntrySp witness) + 2000 < 0 + 1073741824)%Z⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@NativeRootState_14d30) := I.
Global Typeclasses Opaque NativeRootState_14d30.
