Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_00 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderValueTransactions.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoadHeader.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCalleeProviders.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologue.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Import ListNotations.

(** This witness records the concrete data that the native proof must relate to
    the abstract [WriteSuccessArgs] value.  The existing block proofs expose
    these fields, but they do not yet establish this relation. *)
Record writeSuccessNativeWitness (Decoded : Type) : Type := {
  writeSuccessEntrySp : bv 64;
  writeSuccessDecodedPointer : bv 64;
  writeSuccessReturnValue : bv 64;
  writeSuccessSavedS0 : bv 64;
  writeSuccessSavedS1 : bv 64;
  writeSuccessSavedS2 : bv 64;
  writeSuccessSavedS3 : bv 64;
  writeSuccessSavedS4 : bv 64;
  writeSuccessSavedS5 : bv 64;
  writeSuccessSavedS6 : bv 64;
  writeSuccessSavedS7 : bv 64;
  writeSuccessSavedS8 : bv 64;
  writeSuccessSavedS9 : bv 64;
  writeSuccessSavedS10 : bv 64;
  writeSuccessSavedS11 : bv 64;
  writeSuccessDecodedBytes : list (bv 8);
  writeSuccessSourceBytes : list (bv 8);
  writeSuccessValues : list (bv 64);
  writeSuccessPayload : list (bv 8);
  writeSuccessTraceTail : spec;
  writeSuccessTransactionBase : Z;
  writeSuccessTransactions : list writeSuccessTransaction;
  writeSuccessTransactionBytes : list (bv 8);
  writeSuccessRawTransactions : list ByteListItem;
  writeSuccessWithdrawalsBase : bv 64;
  writeSuccessWithdrawalsBytes : list (bv 8);
  writeSuccessWithdrawalsCount : nat;
  writeSuccessPostData : WriteSuccessPostTransactionData
}.

Arguments writeSuccessEntrySp {Decoded} _.
Arguments writeSuccessDecodedPointer {Decoded} _.
Arguments writeSuccessReturnValue {Decoded} _.
Arguments writeSuccessSavedS0 {Decoded} _.
Arguments writeSuccessSavedS1 {Decoded} _.
Arguments writeSuccessSavedS2 {Decoded} _.
Arguments writeSuccessSavedS3 {Decoded} _.
Arguments writeSuccessSavedS4 {Decoded} _.
Arguments writeSuccessSavedS5 {Decoded} _.
Arguments writeSuccessSavedS6 {Decoded} _.
Arguments writeSuccessSavedS7 {Decoded} _.
Arguments writeSuccessSavedS8 {Decoded} _.
Arguments writeSuccessSavedS9 {Decoded} _.
Arguments writeSuccessSavedS10 {Decoded} _.
Arguments writeSuccessSavedS11 {Decoded} _.
Arguments writeSuccessDecodedBytes {Decoded} _.
Arguments writeSuccessSourceBytes {Decoded} _.
Arguments writeSuccessValues {Decoded} _.
Arguments writeSuccessPayload {Decoded} _.
Arguments writeSuccessTraceTail {Decoded} _.
Arguments writeSuccessTransactionBase {Decoded} _.
Arguments writeSuccessTransactions {Decoded} _.
Arguments writeSuccessTransactionBytes {Decoded} _.
Arguments writeSuccessRawTransactions {Decoded} _.
Arguments writeSuccessWithdrawalsBase {Decoded} _.
Arguments writeSuccessWithdrawalsBytes {Decoded} _.
Arguments writeSuccessWithdrawalsCount {Decoded} _.
Arguments writeSuccessPostData {Decoded} _.

Definition writeSuccessFrameSp {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : bv 64 :=
  (writeSuccessEntrySp witness - BV 64 2000)%bv.

Definition writeSuccessNativeTailEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  writeSuccessHeaderEvents (writeSuccessFrameSp witness)
    (writeSuccessValueEvents (writeSuccessFrameSp witness)
      (writeSuccessValues witness)
      (writeSuccessTransactionsEvents (writeSuccessFrameSp witness)
        (writeSuccessTransactions witness)
        (writeSuccessAfterTransactionsEvents (writeSuccessFrameSp witness)
          (writeSuccessWithdrawalsCount witness)
          (writeSuccessPostData witness) (writeSuccessTraceTail witness)))).

Definition writeSuccessNativeAfterTagEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  writeSuccessHeaderEventsAfterTag (writeSuccessFrameSp witness)
    (writeSuccessValueEvents (writeSuccessFrameSp witness)
      (writeSuccessValues witness)
      (writeSuccessTransactionsEvents (writeSuccessFrameSp witness)
        (writeSuccessTransactions witness)
        (writeSuccessAfterTransactionsEvents (writeSuccessFrameSp witness)
          (writeSuccessWithdrawalsCount witness)
          (writeSuccessPostData witness) (writeSuccessTraceTail witness)))).

Definition writeSuccessWitnessWellFormed {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    : Prop :=
  successStackPointer Decoded args = bv_unsigned (writeSuccessEntrySp witness) /\
  successDecodedAddress Decoded args = bv_unsigned (writeSuccessDecodedPointer witness) /\
  successReturnAddress Decoded args = 0x14d10 /\
  writeSuccessReturnValue witness =
    Z_to_bv 64 (successReturnAddress Decoded args) /\
  bv_unsigned (writeSuccessDecodedPointer witness) =
    (bv_unsigned (writeSuccessEntrySp witness) + 32)%Z /\
  length (writeSuccessDecodedBytes witness) = 848%nat /\
  length (writeSuccessSourceBytes witness) = 720%nat /\
  writeSuccessSourceBytes witness =
    take 720 (writeSuccessDecodedBytes witness) /\
  length (writeSuccessValues witness) = 74%nat /\
  bytes_of_u64s (writeSuccessValues witness) =
    take 592 (writeSuccessSourceBytes witness) /\
  bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 5) =
    Z.of_nat (length (writeSuccessPayload witness)) /\
  writeSuccessValueWord (writeSuccessValues witness) 7 =
    Z_to_bv 64 (writeSuccessTransactionBase witness) /\
  writeSuccessValueWord (writeSuccessValues witness) 8 =
    Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactions witness))) /\
  writeSuccessTransactionBytes witness =
    writeSuccessTransactionsBytes (writeSuccessTransactions witness) /\
  writeSuccessMemoryRepresents
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness)
    (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness)
    (successDecoded Decoded args) /\
  writeSuccessTransactionsPost15674ByteListFacts
    (writeSuccessFrameSp witness)
    (writeSuccessValueWord (writeSuccessValues witness) 9)
    (writeSuccessValueWord (writeSuccessValues witness) 10)
    (writeSuccessRawTransactions witness) /\
  writeSuccessValueWord (writeSuccessValues witness) 11 =
    writeSuccessWithdrawalsBase witness /\
  writeSuccessValueWord (writeSuccessValues witness) 12 =
    Z_to_bv 64 (Z.of_nat (writeSuccessWithdrawalsCount witness)) /\
  length (writeSuccessWithdrawalsBytes witness) =
    (48 * writeSuccessWithdrawalsCount witness)%nat /\
  (0x20000000 <= bv_unsigned (writeSuccessWithdrawalsBase witness))%Z /\
  (bv_unsigned (writeSuccessWithdrawalsBase witness) +
    Z.of_nat (length (writeSuccessWithdrawalsBytes witness)) < 0x40000000)%Z /\
  bv_unsigned (writeSuccessEntrySp witness) `mod` 16 = 0 /\
  (0x20000880 <= bv_unsigned (writeSuccessEntrySp witness))%Z /\
  (bv_unsigned (writeSuccessEntrySp witness) + 0x7d0 < 0x40000000)%Z.

(** The existing trace assertions describe output stores.  A later theorem must
    define this relation from those stores to the public byte string. *)
Definition WriteSuccessOutputRelation (Decoded : Type) : Type :=
  WriteSuccessArgs Decoded -> writeSuccessNativeWitness Decoded ->
  ByteString -> Prop.

(** These resources contain every non-callee-stack memory region owned at the
    public entry.  The complete contract returns the same resources. *)
Definition writeSuccessNativeDataResources `{!islaG Sigma}
    `{!threadG} {Decoded} (witness : writeSuccessNativeWitness Decoded) :
    iProp Sigma :=
  writeSuccessLoadHeaderHeapResources
    (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness)
    (writeSuccessValues witness) (writeSuccessPayload witness)
    (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
    (writeSuccessTransactionBytes witness) ∗
  byteListItemResources
    (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 9))
    (writeSuccessRawTransactions witness) ∗
  bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗
    writeSuccessWithdrawalsBytes witness ∗
  ⌜writeSuccessTransactionsPost15674ByteListFacts
    (writeSuccessFrameSp witness)
    (writeSuccessValueWord (writeSuccessValues witness) 9)
    (writeSuccessValueWord (writeSuccessValues witness) 10)
    (writeSuccessRawTransactions witness)⌝ ∗
  ⌜writeSuccessValueWord (writeSuccessValues witness) 11 =
    writeSuccessWithdrawalsBase witness⌝ ∗
  ⌜writeSuccessValueWord (writeSuccessValues witness) 12 =
    Z_to_bv 64 (Z.of_nat (writeSuccessWithdrawalsCount witness))⌝ ∗
  ⌜length (writeSuccessWithdrawalsBytes witness) =
    (48 * writeSuccessWithdrawalsCount witness)%nat⌝ ∗
  ⌜0x20000000 <= bv_unsigned (writeSuccessWithdrawalsBase witness)⌝ ∗
  ⌜bv_unsigned (writeSuccessWithdrawalsBase witness) +
    Z.of_nat (length (writeSuccessWithdrawalsBytes witness)) < 0x40000000⌝ ∗
  writeSuccessPostTransactionDataResources
    (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness)
    (writeSuccessDecodedBytes witness) (writeSuccessPostData witness).

Global Instance : LithiumUnfold (@writeSuccessNativeDataResources) := I.

Definition writeSuccessNativeExitMemory `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  (writeSuccessNativeDataResources witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
     writeSuccessDecodedBytes witness)%I.

Global Instance : LithiumUnfold (@writeSuccessNativeExitMemory) := I.

Definition writeSuccessNativeAllows {Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop) :
    WriteSuccessArgs Decoded -> ByteString -> Prop := allows.

Lemma writeSuccessNativeAllows_exact {Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop) args bytes :
  writeSuccessNativeAllows allows args bytes <-> allows args bytes.
Proof. reflexivity. Qed.

Definition writeSuccessTerminalSavedSlots `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  ((bv_unsigned (writeSuccessFrameSp witness) + 1992) ↦ₘ
     writeSuccessReturnValue witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1984) ↦ₘ
     writeSuccessSavedS0 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1976) ↦ₘ
     writeSuccessSavedS1 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1968) ↦ₘ
     writeSuccessSavedS2 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1960) ↦ₘ
     writeSuccessSavedS3 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1952) ↦ₘ
     writeSuccessSavedS4 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1944) ↦ₘ
     writeSuccessSavedS5 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1936) ↦ₘ
     writeSuccessSavedS6 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1928) ↦ₘ
     writeSuccessSavedS7 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1920) ↦ₘ
     writeSuccessSavedS8 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1912) ↦ₘ
     writeSuccessSavedS9 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1904) ↦ₘ
     writeSuccessSavedS10 witness ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1896) ↦ₘ
     writeSuccessSavedS11 witness ∗ True)%I.

Definition writeSuccessTerminalMachine `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessOtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (writeSuccessReturnValue witness) ∗
   "x2" ↦ᵣ RVal_Bits (writeSuccessEntrySp witness) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessSavedS0 witness) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessSavedS1 witness) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessSavedS2 witness) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessSavedS3 witness) ∗
   "x20" ↦ᵣ RVal_Bits (writeSuccessSavedS4 witness) ∗
   "x21" ↦ᵣ RVal_Bits (writeSuccessSavedS5 witness) ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessSavedS6 witness) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessSavedS7 witness) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessSavedS8 witness) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessSavedS9 witness) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessSavedS10 witness) ∗
   "x27" ↦ᵣ RVal_Bits (writeSuccessSavedS11 witness) ∗
   writeSuccessTerminalSavedSlots witness)%I.

Definition writeSuccessTerminalResources `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) (bytes : ByteString) :
    iProp Sigma :=
  (∃ witness : writeSuccessNativeWitness Decoded,
    ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
    ⌜outputRelation args witness bytes⌝ ∗
    writeSuccessTerminalMachine witness ∗
    writeSuccessNativeExitMemory witness ∗
    spec_trace (writeSuccessTraceTail witness))%I.

Definition writeSuccessHeaderTerminal `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) : iProp Sigma :=
  (instr_pre 0x14d10
    (∃ bytes : ByteString,
      ⌜writeSuccessNativeAllows allows args bytes⌝ ∗
      writeSuccessTerminalResources outputRelation args bytes))%I.

Definition writeSuccessLoadHeaderWithFramePre `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    : iProp Sigma :=
  (instr_pre 0x14d80
    (writeSuccessAtLoadHeaderWithFrame
      (writeSuccessFrameSp witness)
      (writeSuccessSourceBytes witness)
      (writeSuccessNativeTailEvents witness)
      (writeSuccessLoadHeaderRemainder
        (writeSuccessHeaderTerminal allows outputRelation args)
      (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness)
      (writeSuccessValues witness) (writeSuccessPayload witness)
      (writeSuccessTraceTail witness) (writeSuccessTransactionBase witness)
        (writeSuccessTransactions witness)
        (writeSuccessTransactionBytes witness))))%I.

(** These downstream continuations support the conditional composition proof.
    They are not part of the public native entry contract. *)
Definition writeSuccessNativeProofAssumptions `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    : iProp Sigma :=
  (writeSuccessLoadHeaderWithFramePre allows outputRelation args witness ∗ True)%I.

Definition writeSuccessProloguePayload `{!islaG Sigma} `{!threadG}
    {Decoded} (witness : writeSuccessNativeWitness Decoded)
    : iProp Sigma :=
  ((bv_unsigned (writeSuccessEntrySp witness) - 0x7d0) ↦ₘ? 1896 ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
     writeSuccessDecodedBytes witness ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessNativeTailEvents witness) ∗
   writeSuccessNativeDataResources witness ∗
   ⌜length (writeSuccessDecodedBytes witness) = 848%nat⌝ ∗
   ⌜(0x20000000 <= bv_unsigned (writeSuccessDecodedPointer witness))%Z⌝ ∗
   ⌜(bv_unsigned (writeSuccessDecodedPointer witness) + 848 <
      0x40000000)%Z⌝ ∗ True)%I.

Definition writeSuccessNativeEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) : iProp Sigma :=
  (∃ witness : writeSuccessNativeWitness Decoded,
    ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
    write_success_prologue_entry
      (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
      (writeSuccessReturnValue witness)
      (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
      (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
      (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
      (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
      (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
      (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
      (writeSuccessProloguePayload witness))%I.

(** This contract is the closed native prefix from the public entry through
    the load-block entry.  Its exit is the exact resource boundary that the
    complete writer proof consumes next. *)
Definition writeSuccessNativeLoadResources {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    `{!islaG Sigma} `{!threadG} :
    IslarisContractResources (WriteSuccessArgs Decoded)
      (writeSuccessNativeWitness Decoded) := {|
  islarisCode := writeSuccessCompleteNativeCode;
  islarisEntry := writeSuccessNativeEntry;
  islarisExit := fun _ witness =>
    writeSuccessAtLoadHeaderWithFrame
      (writeSuccessFrameSp witness)
      (take 720 (writeSuccessDecodedBytes witness))
      (writeSuccessNativeTailEvents witness)
      (reg_col writeSuccessLoadHeaderExtraRegisters ∗
       writeSuccessNativeDataResources witness)
|}.

Definition writeSuccessNativeLoadAllows {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : Prop :=
  writeSuccessWitnessWellFormed args witness.

Definition writeSuccessNativeLoadModel {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (nextPc : Z -> Z -> Prop) :
    IslarisContractModel (WriteSuccessArgs Decoded)
      (writeSuccessNativeWitness Decoded) := {|
  islarisContractAllows := writeSuccessNativeLoadAllows;
  islarisContractStep := nextPc;
  islarisContractResources := fun Sigma HG HT =>
    @writeSuccessNativeLoadResources Decoded _ Sigma HG HT
|}.

Theorem write_success_native_load_state_correct {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x14d30 0x14d80
    (@writeSuccessNativeLoadAllows Decoded _)
    (@writeSuccessNativeLoadResources Decoded _ Sigma _ _).
Proof.
  rewrite /IslarisContractSpec /writeSuccessNativeLoadResources /=.
  iStartProof.
  iIntros "#Hnative" (args).
  rewrite instr_pre'_eq. iIntros "Hcontract".
  iDestruct "Hcontract" as "[Hentry Hexit]".
  iEval (rewrite /writeSuccessNativeEntry) in "Hentry".
  iDestruct "Hentry" as (witness) "[%HwellFormed Hentry]".
  pose proof HwellFormed as HwellFormedCopy.
  destruct HwellFormed as
    (Hstack & HdecodedAddress & HreturnAddress & HreturnValue &
     Hdecoded & HdecodedLength & HsourceLength & HsourceBytes &
     HvaluesLength & HvaluesBytes & HpayloadLength & Hbase & Hcount &
     HtransactionBytes & Hrepresentation & HrawFacts & HwithdrawalBase & HwithdrawalCount &
     HwithdrawalLength & HwithdrawalMin & HwithdrawalMax & HspAlign & HspMin &
     HspMax).
  have HdecodedMin :
      (0x20000000 <= bv_unsigned (writeSuccessDecodedPointer witness))%Z
    by lia.
  have HdecodedMax :
      (bv_unsigned (writeSuccessDecodedPointer witness) + 848 <
       0x40000000)%Z by lia.
  have HspExtract :
      bv_extract 0 4 (writeSuccessEntrySp witness) = BV 4 0.
  { apply bv_eq. rewrite bv_extract_0_unsigned.
    unfold bv_wrap, bv_modulus. cbn. exact HspAlign. }
  iPoseProof (write_success_native_callee_providers with
    "Hnative") as "#Hcallees".
  iEval (rewrite /writeSuccessNativeCalleeProviders) in "Hcallees".
  iDestruct "Hcallees" as
    "(#Houtput & #Hmemcpy & #Hboolean & #Hoptional & #HbyteLists &
      #Hbytes & #Hu256 & #Hint1645 & #Hint & _)".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as
    "(#Hprologue & #Hlookup & #Hmain & #HoutputCode & #HmemcpyCode &
      #HbooleanCode & #HoptionalCode & #HbyteListsCode & #HbytesCode &
      #HintCode & #Hu256Code & #Hint1645Code)".
  iEval (rewrite -instr_pre'_eq) in "Hexit".
  iAssert (instr_pre 0x14d80
      (writeSuccessAtLoadHeaderWithFrame
        (writeSuccessFrameSp witness)
        (take 720 (writeSuccessDecodedBytes witness))
        (writeSuccessNativeTailEvents witness)
        (reg_col writeSuccessLoadHeaderExtraRegisters ∗
         writeSuccessNativeDataResources witness)))%I
    with "[Hexit]" as "Hload".
  { iApply (instr_pre_wand with "Hexit");
      [done | done |].
    iIntros "Hload".
    iExists witness. iSplit; first (iPureIntro; exact HwellFormedCopy).
    iExact "Hload". }
  iPoseProof (write_success_prologue
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
    (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
    (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
    (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
    (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
    (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessProloguePayload witness) with "Hprologue") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  iSplitL "Hentry"; first iExact "Hentry".
  iSplit; last done.
  iNext. iIntros "Hhandoff".
  iPoseProof (write_success_to_load_with_frame_extra
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
    (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
    (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
    (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
    (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
    (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessDecodedBytes witness) (writeSuccessNativeAfterTagEvents witness)
    (writeSuccessNativeDataResources witness)
    Hdecoded HspExtract HspMin HspMax with
    "Hlookup Hmain HmemcpyCode HoutputCode Hmemcpy Houtput Hload") as "HtoLoad".
  iEval (rewrite instr_pre'_eq) in "HtoLoad".
  iApply "HtoLoad". iExact "Hhandoff".
Qed.

Definition writeSuccessNativeLoadCorrectness {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (nextPc : Z -> Z -> Prop) : Prop :=
  IslarisContractCorrect 0x14d30 0x14d80
    (writeSuccessNativeLoadModel (Decoded := Decoded) nextPc).

Theorem write_success_native_load_correct {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (nextPc : Z -> Z -> Prop) :
  writeSuccessNativeLoadCorrectness (Decoded := Decoded) nextPc.
Proof.
  intros Sigma HG HT. apply write_success_native_load_state_correct.
Qed.

Definition writeSuccessNativeCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  writeSuccessCompleteNativeCode.

Definition writeSuccessNativeResources {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (outputRelation : WriteSuccessOutputRelation Decoded)
    `{!islaG Sigma} `{!threadG} :
    IslarisContractResources (WriteSuccessArgs Decoded) ByteString := {|
  islarisCode := writeSuccessNativeCode;
  islarisEntry := writeSuccessNativeEntry;
  islarisExit := writeSuccessTerminalResources outputRelation
|}.

Definition writeSuccessNativeModel {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (nextPc : Z -> Z -> Prop) :
    IslarisContractModel (WriteSuccessArgs Decoded) ByteString := {|
  islarisContractAllows := writeSuccessNativeAllows allows;
  islarisContractStep := nextPc;
  islarisContractResources := fun Sigma HG HT =>
    @writeSuccessNativeResources Decoded _ outputRelation Sigma HG HT
|}.

(** A native correctness proof needs this semantic premise in addition to the
    machine-resource handoff and the CFG certificate. *)
Definition writeSuccessSemanticPremise {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded) : Prop :=
  forall args witness bytes,
    writeSuccessWitnessWellFormed args witness ->
    outputRelation args witness bytes ->
    allows args bytes.
