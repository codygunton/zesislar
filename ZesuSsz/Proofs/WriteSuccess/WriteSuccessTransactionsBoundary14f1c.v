Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

Definition writeSuccessTransactions14f1cOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x26";
   "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactions14f1cOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
    writeSuccessTransactions14f1cOtherRegisters.

Definition writeSuccessTransactionRestOwn `{!islaG Sigma}
    (transaction : writeSuccessTransaction) : iProp Sigma :=
  (writeSuccessByteArrayOwn
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

Global Typeclasses Opaque writeSuccessTransactionRestOwn.

Definition writeSuccessTransactionsCurrentPhaseFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
     writeSuccessTransactionsBytes remaining ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessByteArrayOwn
     (writeSuccessTransactionDataPointer transaction)
     (writeSuccessTransactionData transaction) ∗
   writeSuccessTransactionRestOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeSuccessTransactionPhaseEvents TransactionType sp transaction
       (writeSuccessTransactionsEvents sp remaining tail)) ∗ P ∗
   writeSuccessTransactionsInvariant sp base transactions processed
     (transaction :: remaining) bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit
       sp base transactions bytes tail P) ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Definition writeSuccessTransactions14f1cFrame
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 128 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 248 + 8) ↦ₘ? 1640 ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 base) ∗
   reg_col writeSuccessTransactions14f1cOtherRegShapes ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactions14f1cFrame.

Definition writeSuccessTransactionsLoadFactsPure
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (processed : list writeSuccessTransaction) (bytes : list (bv 8)) : Prop :=
  length (writeSuccessTransactionBytes transaction) = 288%nat /\
  (base + 288 * Z.of_nat (length processed)) `mod` 8 = 0 /\
  0x20000000 <= base + 288 * Z.of_nat (length processed) /\
  base + 288 * Z.of_nat (length processed) + 288 < 0x40000000 /\
  bv_unsigned sp `mod` 8 = 0 /\
  0x20000000 <= bv_unsigned sp - 48 /\
  bv_unsigned sp + 1896 < 0x40000000.

Definition writeSuccessTransactionsLoadFacts `{!islaG Sigma}
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (processed : list writeSuccessTransaction) (bytes : list (bv 8)) :
    iProp Sigma :=
  (⌜length (writeSuccessTransactionBytes transaction) = 288%nat⌝ ∗
   ⌜(base + 288 * Z.of_nat (length processed)) `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= base + 288 * Z.of_nat (length processed)⌝ ∗
   ⌜base + 288 * Z.of_nat (length processed) + 288 < 0x40000000⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsLoadFacts) := I.

Lemma write_success_transactions_current_base_aligned
    (base : Z) (processedLength : nat) :
  base `mod` 8 = 0 ->
  (base + 288 * Z.of_nat processedLength) `mod` 8 = 0.
Proof.
  intros HbaseAlign.
  replace (base + 288 * Z.of_nat processedLength) with
    (base + (36 * Z.of_nat processedLength) * 8) by ring.
  rewrite Z_mod_plus_full. exact HbaseAlign.
Qed.

Lemma write_success_transactions_current_base_lower
    (base : Z) (processedLength : nat) :
  0x20000000 <= base ->
  0x20000000 <= base + 288 * Z.of_nat processedLength.
Proof. intros HbaseLower. assert (0 <= Z.of_nat processedLength) by lia. nia. Qed.

Lemma write_success_transactions_current_end_upper
    (base : Z) (processedLength remainingLength : nat)
    (bytes prefix suffix : list (bv 8)) :
  bytes = prefix ++ suffix ->
  length prefix = (288 * processedLength)%nat ->
  length suffix = (288 * S remainingLength)%nat ->
  base + Z.of_nat (length bytes) < 0x40000000 ->
  base + 288 * Z.of_nat processedLength + 288 < 0x40000000.
Proof.
  intros HbytesApp HprefixLength HsuffixLength HbaseUpper.
  rewrite HbytesApp length_app HprefixLength HsuffixLength in HbaseUpper.
  lia.
Qed.

Lemma write_success_transactions_stack_aligned_8 (sp : bv 64) :
  bv_unsigned sp `mod` 16 = 0 ->
  bv_unsigned sp `mod` 8 = 0.
Proof.
  intros HspAlign.
  apply Z.mod_divide; [lia|].
  apply Z.mod_divide in HspAlign; [|lia].
  destruct HspAlign as [factor Hfactor].
  exists (2 * factor). lia.
Qed.

Lemma write_success_transactions_load_facts_pure
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) :
  length (writeSuccessTransactionBytes transaction) = 288%nat ->
  bytes = prefix ++ suffix ->
  length prefix = (288 * length processed)%nat ->
  length suffix = (288 * length (transaction :: remaining))%nat ->
  base `mod` 8 = 0 ->
  0x20000000 <= base ->
  base + Z.of_nat (length bytes) < 0x40000000 ->
  bv_unsigned sp `mod` 16 = 0 ->
  0x20000000 <= bv_unsigned sp - 48 ->
  bv_unsigned sp + 1896 < 0x40000000 ->
  writeSuccessTransactionsLoadFactsPure sp base transaction processed bytes.
Proof.
  intros HtransactionLength HbytesApp HprefixLength HsuffixLength
    HbaseAlign HbaseLower HbaseUpper HspAlign HspLower HspUpper.
  rewrite /writeSuccessTransactionsLoadFactsPure.
  split; first exact HtransactionLength.
  split; first exact (write_success_transactions_current_base_aligned
    base (length processed) HbaseAlign).
  split; first exact (write_success_transactions_current_base_lower
    base (length processed) HbaseLower).
  split; first exact (write_success_transactions_current_end_upper
    base (length processed) (length remaining) bytes prefix suffix
    HbytesApp HprefixLength HsuffixLength HbaseUpper).
  split; first exact (write_success_transactions_stack_aligned_8 sp HspAlign).
  repeat split; assumption.
Qed.

Lemma write_success_transactions_current_load_facts
    `{!islaG Sigma} (sp : bv 64) (base : Z)
    (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) :
  writeSuccessTransactionValid transaction ->
  writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix -∗
  writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
  ⌜suffix = writeSuccessTransactionBytes transaction ++
    writeSuccessTransactionsBytes remaining⌝.
Proof.
  iIntros (Hvalid) "Hinv".
  iEval (unfold writeSuccessTransactionsInvariant) in "Hinv".
  iDestruct "Hinv" as
    "(%Htransactions & %Hbytes & %Hprefix & %Hsuffix & %HbytesApp &
     %HbytesLength & %HprefixLength & %HsuffixLength & %HtotalBound &
     %HspAlign & %HspLower & %HspUpper & %HbaseAlign & %HbaseLower &
     %HbaseUpper & _)".
  destruct Hvalid as [HtransactionLength _].
  pose proof (write_success_transactions_load_facts_pure sp base transaction
    processed remaining bytes prefix suffix HtransactionLength HbytesApp
    HprefixLength HsuffixLength HbaseAlign HbaseLower HbaseUpper HspAlign
    HspLower HspUpper) as Hfacts.
  destruct Hfacts as
    (HtransactionLength' & HcurrentAlign & HcurrentLower & HcurrentUpper &
     HstackAlign & HstackLower & HstackUpper).
  iSplit.
  - rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done.
  - iPureIntro. rewrite Hsuffix /=. done.
Qed.

Definition writeSuccessTransactionsAt14f1cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x25" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ ([] : list (bv 8)) ∗
    writeSuccessTransactions14f1cFrame sp base transactions processed ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt14f1cSpec) := I.
