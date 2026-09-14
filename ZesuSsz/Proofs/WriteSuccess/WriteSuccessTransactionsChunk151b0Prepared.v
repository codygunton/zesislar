Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151acReturn.

Import ListNotations WriteSuccessTransactionsSpec.

Definition writeSuccessTransactions151b0CallFrame
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (b5 b12 b13 b14 b15 b16 b17 : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits b5 ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     ["x6"; "x7"; "x28"; "x29"; "x30"; "x31"]) ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
   "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
   "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
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
   "x2" ↦ᵣ RVal_Bits sp ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48 /\ bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (WriteSuccessEvents.writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 32)
       (writeSuccessTransactionPhaseEvents TransactionData sp transaction
         (writeSuccessTransactionsEvents sp remaining tail))) ∗
   instr_pre 0x151b4
     (writeSuccessTransactions151acCallRet sp transaction remaining tail) ∗
   True)%I.

Definition writeSuccessTransactions151b0PreparedSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (sp : bv 64) (b5 b12 b13 b14 b15 b16 b17 : bv 64)
      (transaction : writeSuccessTransaction)
      (remaining : list writeSuccessTransaction) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 86444 + 4096)%bv ∗
    writeSuccessTransactions151b0CallFrame sp b5 b12 b13 b14 b15 b16 b17
      transaction remaining tail ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions151b0PreparedSpec) := I.

Lemma write_success_transactions_151b0_call
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (b5 b12 b13 b14 b15 b16 b17 : bv 64)
    (transaction : writeSuccessTransaction)
    (remaining : list writeSuccessTransaction) (tail : spec) :
  reg_col zesu_ram_sys_regs -∗
  "x1" ↦ᵣ RVal_Bits (BV 64 0x151b4) -∗
  writeSuccessTransactions151b0CallFrame sp b5 b12 b13 b14 b15 b16 b17
      transaction remaining tail -∗
  zesuEncoderU256CallSpec.
Proof.
  iStartProof. iIntros "Hsys H1 Hframe".
  iEval (unfold writeSuccessTransactions151b0CallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(H5 & Htmp & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H8 &
      H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
      H2 & %Halign & %Hbounds & Hstack & Hmmio & Htrace & Hreturn & _)".
  iPoseProof (write_success_transactions_151ac_call_entry_intro
    sp b5 b12 b13 b14 b15 b16 b17 transaction remaining tail Halign Hbounds
    with "Hsys H5 Htmp H10 H11 H12 H13 H14 H15 H16 H17 H8 H9 H18 H19 H20
      H21 H22 H23 H24 H25 H26 H27 H1 H2 Hstack Hmmio Htrace Hreturn")
    as "Hentry".
  iApply (write_success_transactions_151ac_call_entry sp b5 b12 b13 b14 b15
    b16 b17 transaction remaining tail with "Hentry").
Qed.
