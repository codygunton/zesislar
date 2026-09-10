From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151b4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations WriteSuccessTransactionsSpec.

Definition writeSuccessTransactions151acOuterFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (base ↦ₘ∗ prefix ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessTransactionsProcessedOwn processed ∗
   writeSuccessTransactionOwn transaction ∗
   writeSuccessTransactionsOwn remaining ∗ P ∗
   writeSuccessTransactionsInvariant
     sp base transactions processed (transaction :: remaining)
     bytes prefix suffix ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions bytes tail P))%I.

Definition writeSuccessTransactions151acSetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜bv_extract 0 3 (sp + 128) = 0%bv⌝ ∗
    ⌜0x20000000 <= bv_unsigned (sp + 128)⌝ ∗
    ⌜bv_unsigned (sp + 128) <= 0x20000000 + 0x20000000 - 8⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    writeSuccessTransactionsMachine151ac
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗
    writeSuccessTransactions151acOuterFrame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗
    instr_body 0x151b4 (writeSuccessTransactionsAt151b4Spec P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions151acSetupSpec) := I.

Definition writeSuccessTransactionsMachine151b0
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     ["x3"; "x4"; "x6"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16";
      "x17"; "x28"; "x29"; "x30"; "x31"]) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 86444 + 4096)%bv ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   ("x5" ↦ᵣ: fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) ∗
   writeSuccessTransactionsScratch1519c
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine151b0) := I.

Definition writeSuccessTransactions151b0SetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    writeSuccessTransactionsMachine151b0
      sp base transactions processed transaction ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗
    writeSuccessTransactions151acOuterFrame P sp base transaction transactions
      processed remaining bytes prefix suffix tail ∗
    instr_body 0x151b4 (writeSuccessTransactionsAt151b4Spec P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions151b0SetupSpec) := I.

Lemma write_success_transactions_151ac_return_frame_intro
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactions151acOuterFrame P sp base transaction transactions
      processed remaining bytes prefix suffix tail -∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x3"; "x4"]) -∗
  ((bv_unsigned sp - 48) ↦ₘ? 48 -∗
    writeSuccessTransactionsScratch1519c
      sp base transactions processed transaction) -∗
  writeSuccessTransactions151acReturnFrame P sp base transaction transactions
    processed remaining bytes prefix suffix tail.
Proof.
  iStartProof. iIntros "Houter H34 Hscratch".
  iEval (unfold writeSuccessTransactions151acOuterFrame) in "Houter".
  rewrite /writeSuccessTransactions151acReturnFrame.
  iFrame.
Qed.

Lemma write_success_transactions_151ac_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x151b4 (writeSuccessTransactionsAt151b4Spec P) -∗
  writeSuccessTransactionsAt151acSpec P -∗
  writeSuccessTransactions151acSetupSpec P.
Proof.
  iStartProof. iIntros "Hnext Hentry".
  iEval (unfold writeSuccessTransactionsAt151acSpec) in "Hentry".
  iDestruct "Hentry" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & %Halign & %Hmin & %Hmax & Hphase)".
  iEval (unfold writeSuccessTransactionPhaseHandoff) in "Hphase".
  iDestruct "Hphase" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & #Hinv & Hexit & _)".
  iEval (unfold writeSuccessTransactionsInvariant) in "Hinv".
  iDestruct "Hinv" as
    "(%Htransactions & %Hbytes & %Hprefix & %Hsuffix & %Happend & %HbytesLen &
      %HprefixLen & %HsuffixLen & %HtransactionsBound & %HspAlign & %HspMin &
      %HspMax & %HbaseAlign & %HbaseMin & %HbaseMax & _)".
  iAssert (writeSuccessTransactionsInvariant sp base transactions processed
      (transaction :: remaining) bytes prefix suffix)%I with "[]" as "Hinv".
  { rewrite /writeSuccessTransactionsInvariant.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  repeat iSplit; try iPureIntro; try assumption.
  iFrame "Hmachine Hmmio Htrace".
  iSplitL "Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit".
  { rewrite /writeSuccessTransactions151acOuterFrame.
    iFrame "Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit". }
  iFrame "Hnext".
Qed.
