Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0Spec.

Definition writeSuccessTransactions150f8SomeCallFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (chainId sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionChainId transaction =
      Some chainId⌝ ∗
   □ ⌜WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 <>
      BV 8 0⌝ ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     writeSuccessTransactions150f8OtherRegisters) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 0x680)%bv ∗
   "x18" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)) ∗
   WriteSuccessTransactionsBoundary150e8.writeSuccessTransactionsScratch150e8
     sp base transactions processed transaction ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
       WriteSuccessTransactionsSpec.TransactionChainId sp transaction
       (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
         sp remaining tail)) ∗
   writeSuccessTransactions150f0Frame P sp base transaction transactions
     processed remaining bytes prefix suffix tail ∗
   instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactions150f8SomeCallFrame.

Definition writeSuccessTransactionsAt15bc8SomeSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (chainId sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x150fc) ∗
    writeSuccessTransactions150f8SomeCallFrame P chainId sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsAt15bc8SomeSpec) := I.

Lemma write_success_transactions_150f8_some_frame_pack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  writeSuccessTransactionsAt150f8SomeSpec P -∗
  ∃ (chainId sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x160f4) ∗
    writeSuccessTransactions150f8SomeCallFrame P chainId sp base transaction
      transactions processed remaining bytes prefix suffix tail.
Proof.
  iIntros "Hnext Hentry".
  rewrite /writeSuccessTransactionsAt150f8SomeSpec.
  iDestruct "Hentry" as
    (chainId sp base transaction transactions processed remaining bytes prefix
      suffix tail) "Hentry".
  iEval (unfold writeSuccessTransactionsAt150f8SomeBlock) in "Hentry".
  iDestruct "Hentry" as
    "(%Hchain & #Htag & Hmachine & Hmmio & Htrace & Hframe & _)".
  iEval (unfold writeSuccessTransactionsMachine150f8) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H8 & H9 & H10 & H18 & H19 & H20 & H21 &
      H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  iExists chainId, sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "Hsys H1".
  rewrite /writeSuccessTransactions150f8SomeCallFrame.
  iSplit; first (iPureIntro; exact Hchain).
  iSplit; first iExact "Htag".
  iFrame.
Qed.
