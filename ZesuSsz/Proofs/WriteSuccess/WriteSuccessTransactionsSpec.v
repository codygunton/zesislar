Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.

Import ListNotations.

Definition writeSuccessTransactionsLoopEntryAddress : Z := 0x14f04.
Definition writeSuccessTransactionsLoopExitAddress : Z := 0x15668.

Record writeSuccessTransaction := {
  writeSuccessTransactionBytes : list (bv 8);
  writeSuccessTransactionType : bv 8;
  writeSuccessTransactionChainId : option (bv 64);
  writeSuccessTransactionNonce : bv 64;
  writeSuccessTransactionGasPrice : bv 64 * bv 64;
  writeSuccessTransactionGasPriorityFee : option (bv 64 * bv 64);
  writeSuccessTransactionGasLimit : bv 64;
  writeSuccessTransactionTo : option (list (bv 8));
  writeSuccessTransactionValue : list (bv 64);
  writeSuccessTransactionDataPointer : bv 64;
  writeSuccessTransactionData : list (bv 8);
  writeSuccessTransactionAccessPointer : bv 64;
  writeSuccessTransactionAccessEntries : list writeSuccessAccessEntry;
  writeSuccessTransactionAccessBytes : list (bv 8);
  writeSuccessTransactionBlobPointer : bv 64;
  writeSuccessTransactionBlobHashes : list (list (bv 8));
  writeSuccessTransactionAuthorizationPointer : bv 64;
  writeSuccessTransactionAuthorizations : list (list (bv 8));
  writeSuccessTransactionMaxFeePerBlobGas : bv 64 * bv 64;
  writeSuccessTransactionV : bv 64;
  writeSuccessTransactionR : list (bv 64);
  writeSuccessTransactionS : list (bv 64);
}.

Definition writeSuccessTransactionWord
    (transaction : writeSuccessTransaction) (offset : nat) : bv 64 :=
  Z_to_bv 64
    (little_endian_to_bv 8
      (take 8 (drop offset (writeSuccessTransactionBytes transaction)))).

Definition writeSuccessTransactionByte
    (transaction : writeSuccessTransaction) (offset : nat) : bv 8 :=
  default (BV 8 0) (writeSuccessTransactionBytes transaction !! offset).

Definition writeSuccessTransactionBlobBytes
    (transaction : writeSuccessTransaction) : list (bv 8) :=
  concat (writeSuccessTransactionBlobHashes transaction).

Definition writeSuccessTransactionAuthorizationBytes
    (transaction : writeSuccessTransaction) : list (bv 8) :=
  concat (writeSuccessTransactionAuthorizations transaction).

Definition writeSuccessTransactionValid
    (transaction : writeSuccessTransaction) : Prop :=
  length (writeSuccessTransactionBytes transaction) = 288%nat /\
  writeSuccessTransactionByte transaction 264 =
    writeSuccessTransactionType transaction /\
  (match writeSuccessTransactionChainId transaction with
   | None => writeSuccessTransactionByte transaction 168 = BV 8 0
   | Some chainId =>
       writeSuccessTransactionByte transaction 168 <> BV 8 0 /\
       writeSuccessTransactionWord transaction 160 = chainId
   end) /\
  writeSuccessTransactionWord transaction 176 =
    writeSuccessTransactionNonce transaction /\
  (writeSuccessTransactionWord transaction 0,
   writeSuccessTransactionWord transaction 8) =
    writeSuccessTransactionGasPrice transaction /\
  (match writeSuccessTransactionGasPriorityFee transaction with
   | None => writeSuccessTransactionByte transaction 32 = BV 8 0
   | Some fee =>
       writeSuccessTransactionByte transaction 32 <> BV 8 0 /\
       (writeSuccessTransactionWord transaction 16,
        writeSuccessTransactionWord transaction 24) = fee
   end) /\
  writeSuccessTransactionWord transaction 184 =
    writeSuccessTransactionGasLimit transaction /\
  (match writeSuccessTransactionTo transaction with
   | None => writeSuccessTransactionByte transaction 285 = BV 8 0
   | Some address =>
       writeSuccessTransactionByte transaction 285 <> BV 8 0 /\
       address = take 20 (drop 265 (writeSuccessTransactionBytes transaction)) /\
       length address = 20%nat
   end) /\
  writeSuccessTransactionValue transaction =
    [writeSuccessTransactionWord transaction 48;
     writeSuccessTransactionWord transaction 56;
     writeSuccessTransactionWord transaction 64;
     writeSuccessTransactionWord transaction 72] /\
  writeSuccessTransactionWord transaction 192 =
    writeSuccessTransactionDataPointer transaction /\
  bv_unsigned (writeSuccessTransactionWord transaction 200) =
    length (writeSuccessTransactionData transaction) /\
  writeSuccessTransactionWord transaction 208 =
    writeSuccessTransactionAccessPointer transaction /\
  bv_unsigned (writeSuccessTransactionWord transaction 216) =
    length (writeSuccessTransactionAccessEntries transaction) /\
  writeSuccessTransactionAccessBytes transaction =
    writeSuccessAccessEntriesBytes
      (writeSuccessTransactionAccessEntries transaction) /\
  writeSuccessTransactionWord transaction 224 =
    writeSuccessTransactionBlobPointer transaction /\
  bv_unsigned (writeSuccessTransactionWord transaction 232) =
    length (writeSuccessTransactionBlobHashes transaction) /\
  Forall (fun hash => length hash = 32%nat)
    (writeSuccessTransactionBlobHashes transaction) /\
  (writeSuccessTransactionWord transaction 80,
   writeSuccessTransactionWord transaction 88) =
    writeSuccessTransactionMaxFeePerBlobGas transaction /\
  writeSuccessTransactionWord transaction 240 =
    writeSuccessTransactionAuthorizationPointer transaction /\
  bv_unsigned (writeSuccessTransactionWord transaction 248) =
    length (writeSuccessTransactionAuthorizations transaction) /\
  Forall (fun authorization => length authorization = 144%nat)
    (writeSuccessTransactionAuthorizations transaction) /\
  writeSuccessTransactionWord transaction 256 =
    writeSuccessTransactionV transaction /\
  writeSuccessTransactionR transaction =
    [writeSuccessTransactionWord transaction 96;
     writeSuccessTransactionWord transaction 104;
     writeSuccessTransactionWord transaction 112;
     writeSuccessTransactionWord transaction 120] /\
  writeSuccessTransactionS transaction =
    [writeSuccessTransactionWord transaction 128;
     writeSuccessTransactionWord transaction 136;
     writeSuccessTransactionWord transaction 144;
     writeSuccessTransactionWord transaction 152].

Definition writeSuccessByteArrayOwn `{!islaG Sigma}
    (pointer : bv 64) (bytes : list (bv 8)) : iProp Sigma :=
  match bytes with
  | [] => True
  | _ :: _ =>
      (bv_unsigned pointer ↦ₘ∗ bytes ∗
       ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
       ⌜bv_unsigned pointer + Z.of_nat (length bytes) < 0x40000000⌝ ∗
       True)%I
  end.

Global Instance : LithiumUnfold (@writeSuccessByteArrayOwn) := I.

Definition writeSuccessTransactionOwn `{!islaG Sigma}
    (transaction : writeSuccessTransaction) : iProp Sigma :=
  (writeSuccessByteArrayOwn
     (writeSuccessTransactionDataPointer transaction)
     (writeSuccessTransactionData transaction) ∗
   writeSuccessByteArrayOwn
     (writeSuccessTransactionAccessPointer transaction)
     (writeSuccessTransactionAccessBytes transaction) ∗
   writeSuccessAccessEntriesOwn
     (writeSuccessTransactionAccessEntries transaction) ∗
   writeSuccessByteArrayOwn
     (writeSuccessTransactionBlobPointer transaction)
     (writeSuccessTransactionBlobBytes transaction) ∗
   writeSuccessByteArrayOwn
     (writeSuccessTransactionAuthorizationPointer transaction)
     (writeSuccessTransactionAuthorizationBytes transaction) ∗
   ⌜writeSuccessTransactionValid transaction⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionOwn) := I.

Fixpoint writeSuccessTransactionsOwn `{!islaG Sigma}
    (transactions : list writeSuccessTransaction) : iProp Sigma :=
  match transactions with
  | [] => True
  | transaction :: transactions =>
      (writeSuccessTransactionOwn transaction ∗
       writeSuccessTransactionsOwn transactions ∗ True)%I
  end.

Global Instance : LithiumUnfold (@writeSuccessTransactionsOwn) := I.

Definition writeSuccessTransactionsProcessedOwn `{!islaG Sigma}
    (transactions : list writeSuccessTransaction) : iProp Sigma :=
  writeSuccessTransactionsOwn transactions.

Global Typeclasses Opaque writeSuccessTransactionsProcessedOwn.

Fixpoint writeSuccessTransactionsBytes
    (transactions : list writeSuccessTransaction) : list (bv 8) :=
  match transactions with
  | [] => []
  | transaction :: transactions =>
      writeSuccessTransactionBytes transaction ++
      writeSuccessTransactionsBytes transactions
  end.

Definition writeSuccessOptionalU64Events (sp : bv 64)
    (value : option (bv 64)) (tail : spec) : spec :=
  match value with
  | None => writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) tail
  | Some _ =>
      writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)
  end.

Definition writeSuccessOptionalU128Events (sp : bv 64)
    (value : option (bv 64 * bv 64)) (tail : spec) : spec :=
  match value with
  | None => writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) tail
  | Some _ =>
      writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 32)%bv (BV 64 16) tail)
  end.

Definition writeSuccessOptionalAddressEvents (sp : bv 64)
    (value : option (list (bv 8))) (tail : spec) : spec :=
  match value with
  | None => writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) tail
  | Some _ =>
      writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 20) tail)
  end.

Definition writeSuccessTransactionEvents (sp : bv 64)
    (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 1)
    (writeSuccessOptionalU64Events sp
      (writeSuccessTransactionChainId transaction)
      (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeOutputEventsAny (sp - BV 64 32)%bv (BV 64 16)
          (writeSuccessOptionalU128Events sp
            (writeSuccessTransactionGasPriorityFee transaction)
            (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
              (writeSuccessOptionalAddressEvents sp
                (writeSuccessTransactionTo transaction)
                (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 32)
                  (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
                    (writeOutputEventsAny
                      (writeSuccessTransactionDataPointer transaction)
                      (Z_to_bv 64
                        (Z.of_nat
                          (length (writeSuccessTransactionData transaction))))
                      (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
                        (writeSuccessAccessListsEvents sp
                          (writeSuccessTransactionAccessEntries transaction)
                          (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
                            (writeSuccessBlobHashesEvents sp
                              (length
                                (writeSuccessTransactionBlobHashes transaction))
                              (writeOutputEventsAny (sp - BV 64 32)%bv (BV 64 16)
                                (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
                                  (writeSuccessAuthorizationsEvents sp
                                    (length
                                      (writeSuccessTransactionAuthorizations
                                        transaction))
                                    (writeOutputEventsAny
                                      (sp - BV 64 16)%bv (BV 64 8)
                                      (writeOutputEventsAny
                                        (sp - BV 64 48)%bv (BV 64 32)
                                        (writeOutputEventsAny
                                          (sp - BV 64 48)%bv (BV 64 32)
                                          tail))))))))))))))))))).

Fixpoint writeSuccessTransactionsEvents (sp : bv 64)
    (transactions : list writeSuccessTransaction) (tail : spec) : spec :=
  match transactions with
  | [] => tail
  | transaction :: transactions =>
      writeSuccessTransactionEvents sp transaction
        (writeSuccessTransactionsEvents sp transactions tail)
  end.

Inductive writeSuccessTransactionPhase :=
  | TransactionType
  | TransactionChainId
  | TransactionNonce
  | TransactionGasPrice
  | TransactionGasPriorityFee
  | TransactionGasLimit
  | TransactionTo
  | TransactionValue
  | TransactionData
  | TransactionAccessCount
  | TransactionAccessEntries
  | TransactionBlobCount
  | TransactionBlobHashes
  | TransactionMaxFeePerBlobGas
  | TransactionAuthorizationCount
  | TransactionAuthorizations
  | TransactionV
  | TransactionR
  | TransactionS
  | TransactionTail.

Definition writeSuccessTransactionPhaseAddress
    (phase : writeSuccessTransactionPhase) : Z :=
  match phase with
  | TransactionType => 0x14f08
  | TransactionChainId => 0x150f0
  | TransactionNonce => 0x150fc
  | TransactionGasPrice => 0x15108
  | TransactionGasPriorityFee => 0x15118
  | TransactionGasLimit => 0x15148
  | TransactionTo => 0x15154
  | TransactionValue => 0x1519c
  | TransactionData => 0x151b4
  | TransactionAccessCount => 0x151c4
  | TransactionAccessEntries => 0x151d0
  | TransactionBlobCount => 0x153c0
  | TransactionBlobHashes => 0x153d0
  | TransactionMaxFeePerBlobGas => 0x15564
  | TransactionAuthorizationCount => 0x15574
  | TransactionAuthorizations => 0x15584
  | TransactionV => 0x15620
  | TransactionR => 0x1562c
  | TransactionS => 0x15644
  | TransactionTail => 0x1565c
  end.

Definition writeSuccessTransactionPhaseEvents
    (phase : writeSuccessTransactionPhase) (sp : bv 64)
    (transaction : writeSuccessTransaction) (tail : spec) : spec :=
  let transactionTail := tail in
  let sEvents := writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 32) transactionTail in
  let rEvents := writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 32) sEvents in
  let vEvents := writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) rEvents in
  let authorizationEvents :=
    writeSuccessAuthorizationsEvents sp
      (length (writeSuccessTransactionAuthorizations transaction)) vEvents in
  let authorizationCountEvents :=
    writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) authorizationEvents in
  let maxFeeEvents :=
    writeOutputEventsAny (sp - BV 64 32)%bv (BV 64 16)
      authorizationCountEvents in
  let blobEvents :=
    writeSuccessBlobHashesEvents sp
      (length (writeSuccessTransactionBlobHashes transaction)) maxFeeEvents in
  let blobCountEvents :=
    writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) blobEvents in
  let accessEvents :=
    writeSuccessAccessListsEvents sp
      (writeSuccessTransactionAccessEntries transaction) blobCountEvents in
  let accessCountEvents :=
    writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) accessEvents in
  let dataEvents :=
    writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
      (writeOutputEventsAny (writeSuccessTransactionDataPointer transaction)
        (Z_to_bv 64
          (Z.of_nat (length (writeSuccessTransactionData transaction))))
        accessCountEvents) in
  let valueEvents :=
    writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 32) dataEvents in
  let toEvents :=
    writeSuccessOptionalAddressEvents sp
      (writeSuccessTransactionTo transaction) valueEvents in
  let gasLimitEvents :=
    writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) toEvents in
  let priorityEvents :=
    writeSuccessOptionalU128Events sp
      (writeSuccessTransactionGasPriorityFee transaction) gasLimitEvents in
  let gasPriceEvents :=
    writeOutputEventsAny (sp - BV 64 32)%bv (BV 64 16) priorityEvents in
  let nonceEvents :=
    writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) gasPriceEvents in
  let chainEvents :=
    writeSuccessOptionalU64Events sp
      (writeSuccessTransactionChainId transaction) nonceEvents in
  match phase with
  | TransactionType =>
      writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 1) chainEvents
  | TransactionChainId => chainEvents
  | TransactionNonce => nonceEvents
  | TransactionGasPrice => gasPriceEvents
  | TransactionGasPriorityFee => priorityEvents
  | TransactionGasLimit => gasLimitEvents
  | TransactionTo => toEvents
  | TransactionValue => valueEvents
  | TransactionData => dataEvents
  | TransactionAccessCount => accessCountEvents
  | TransactionAccessEntries => accessEvents
  | TransactionBlobCount => blobCountEvents
  | TransactionBlobHashes => blobEvents
  | TransactionMaxFeePerBlobGas => maxFeeEvents
  | TransactionAuthorizationCount => authorizationCountEvents
  | TransactionAuthorizations => authorizationEvents
  | TransactionV => vEvents
  | TransactionR => rEvents
  | TransactionS => sEvents
  | TransactionTail => transactionTail
  end.

Definition writeSuccessTransactionsOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18"; "x19";
   "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactionsOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactionsOtherRegisters.

Definition writeSuccessTransactionsScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total : nat) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 1776 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch) := I.

Definition writeSuccessTransactionsInvariant `{!islaG Sigma}
    (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) : iProp Sigma :=
  (⌜transactions = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessTransactionsBytes transactions⌝ ∗
   ⌜prefix = writeSuccessTransactionsBytes processed⌝ ∗
   ⌜suffix = writeSuccessTransactionsBytes remaining⌝ ∗
   ⌜bytes = prefix ++ suffix⌝ ∗
   ⌜length bytes = (288 * length transactions)%nat⌝ ∗
   ⌜length prefix = (288 * length processed)%nat⌝ ∗
   ⌜length suffix = (288 * length remaining)%nat⌝ ∗
   ⌜(length transactions < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   ⌜base `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsInvariant) := I.

Definition writeSuccessTransactionsLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions : list writeSuccessTransaction) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsScratch sp base (length transactions) ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsLoopExit) := I.

Definition writeSuccessTransactionsLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactionsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
    "x11" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length processed))) ∗
    base ↦ₘ∗ prefix ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessTransactionsOwn processed ∗
    writeSuccessTransactionsOwn remaining ∗
    writeSuccessTransactionsScratch sp base (length transactions) ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessTransactionsEvents sp remaining tail) ∗ P ∗
    writeSuccessTransactionsInvariant
      sp base transactions processed remaining bytes prefix suffix ∗
    instr_pre writeSuccessTransactionsLoopExitAddress
      (writeSuccessTransactionsLoopExit
        sp base transactions bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsLoopSpec) := I.

Definition writeSuccessTransactionPhaseHandoff `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessTransactionPhase) (machine : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (machine ∗ base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeSuccessTransactionPhaseEvents phase sp transaction
       (writeSuccessTransactionsEvents sp remaining tail)) ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit
       sp base transactions bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionPhaseHandoff) := I.
