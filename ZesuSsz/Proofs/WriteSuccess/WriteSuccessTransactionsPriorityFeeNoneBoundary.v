Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15118.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.

Import ListNotations.

Definition writeSuccessTransactionsPriorityFeeCallerShapes :
    list (reg_kind * valu_shape) :=
  (fun r => (KindReg r, BitsShape 64)) <$>
    ["x12"; "x13"; "x14"; "x15"; "x16"; "x17"].

Definition writeSuccessTransactionsPriorityFeeSavedShapes
    (transaction : writeSuccessTransaction) : list (reg_kind * valu_shape) :=
  [(KindReg "x8", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 192)));
   (KindReg "x9", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 16)));
   (KindReg "x18", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 48)));
   (KindReg "x19", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 224)));
   (KindReg "x20", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 56)));
   (KindReg "x21", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 72)));
   (KindReg "x22", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 200)));
   (KindReg "x23", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 24)));
   (KindReg "x24", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 8)));
   (KindReg "x25", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 0)));
   (KindReg "x26", ExactShape
      (RVal_Bits (writeSuccessTransactionWord transaction 184)));
   (KindReg "x27", ExactShape
      (RVal_Bits (bv_zero_extend 64
        (writeSuccessTransactionByte transaction 32))))].

Definition writeSuccessTransactionsPriorityFeeMachineCallerFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
   ((bv_unsigned sp - 16) ↦ₘ? 16 -∗
     writeSuccessTransactionsScratch150e8
       sp base transactions processed transaction) ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeMachineCallerFrame.

Definition writeSuccessTransactionsPriorityFeeCallerFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsPriorityFeeMachineCallerFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsPriorityFeeFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeCallerFrame.

Definition writeSuccessTransactionsPriorityFeeBooleanSetupSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (entryX1 : bv 64) (entryX10 : bv 64 -> bv 64) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    reg_col writeSuccessTransactionsPriorityFeeCallerShapes ∗
    reg_col (writeSuccessTransactionsPriorityFeeSavedShapes transaction) ∗
    "x1" ↦ᵣ RVal_Bits entryX1 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits (entryX10 sp) ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
        (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
          (writeSuccessTransactionsEvents sp remaining tail))) ∗
    writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeBooleanSetupSpec) := I.

Definition writeSuccessTransactionsPriorityFeeNoneAt1513cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  writeSuccessTransactionsPriorityFeeBooleanSetupSpec P
    (BV 64 0x15118) (fun sp => (sp - BV 64 32)%bv).

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeNoneAt1513cSpec) := I.

Definition writeSuccessTransactionsPriorityFeeNoneAt15144Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  writeSuccessTransactionsPriorityFeeBooleanSetupSpec P
    (BV 64 0x16140) (fun _ => BV 64 0).

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeNoneAt15144Spec) := I.
