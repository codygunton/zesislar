Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalCountModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Open Scope Z_scope.

Definition exactTailWithdrawalCountOtherCallerShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
  ["x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x6"; "x7"; "x28"; "x29"; "x30"; "x31"].

Definition exactTailWithdrawalCommonFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) (savedShapes : list (reg_kind * valu_shape))
    : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (reg_col exactTailWithdrawalCountOtherCallerShapes ∗
   reg_col savedShapes ∗
   reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessValueWord values 11) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessValueWord values 12) ∗
   (bv_unsigned sp - 80) ↦ₘ? 64 ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
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
Definition exactTailWithdrawalCountFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  exactTailWithdrawalCommonFrame args witness P
    exactTailWithdrawalLoadSavedShapes.

Definition exactTailWithdrawalBranchFrame `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  exactTailWithdrawalCommonFrame args witness P
    (tl exactTailWithdrawalLoadSavedShapes).

Global Instance : LithiumUnfold (@exactTailWithdrawalCommonFrame) := I.
Global Instance : LithiumUnfold (@exactTailWithdrawalBranchFrame) := I.
Global Instance : LithiumUnfold (@exactTailWithdrawalCountFrame) := I.

Definition exactTailWithdrawalCountReturn `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  encoderIntExactFramedPost (writeSuccessFrameSp witness) (BV 64 0x1568c)
    (exactTailAfterWithdrawalCountEvents witness)
    (exactTailWithdrawalCountFrame args witness P).
Global Instance : LithiumUnfold (@exactTailWithdrawalCountReturn) := I.

Definition exactTailWithdrawalCountCallEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let count := writeSuccessValueWord (writeSuccessValues witness) 12 in
  (∃ old5 old11 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15684) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old5 ∗ "x10" ↦ᵣ RVal_Bits count ∗
    "x11" ↦ᵣ RVal_Bits old11 ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (exactTailAfterRawEvents witness) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < machineRamEnd defaultMap⌝ ∗
    ⌜bv_unsigned count = Z.of_nat (writeSuccessWithdrawalsCount witness)⌝ ∗
    exactTailWithdrawalCountFrame args witness P ∗
    instr_pre (bv_unsigned (BV 64 0x1568c))
      (exactTailWithdrawalCountReturn args witness P) ∗ True)%I.
Global Instance : LithiumUnfold (@exactTailWithdrawalCountCallEntry) := I.
