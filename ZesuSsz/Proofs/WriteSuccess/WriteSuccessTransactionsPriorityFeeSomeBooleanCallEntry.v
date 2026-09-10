Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanAbiFinalize.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanAbiTail.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanRegisters.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanReturnPre.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanPreparedSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    reg_col writeSuccessTransactionsPriorityFeeCallerShapes ∗
    reg_col (writeSuccessTransactionsPriorityFeeSavedShapes transaction) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15128) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits (BV 64 1) ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessTransactionsPriorityFeeSomeBooleanEvents
        sp transaction remaining tail) ∗
    writeSuccessTransactionsPriorityFeeCallerFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeSomeBooleanPreparedSpec) := I.

Lemma write_success_transactions_priority_fee_some_boolean_call_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x15128
    (writeSuccessTransactionsPriorityFeeSomeAt15128Spec P) -∗
  writeSuccessTransactionsPriorityFeeSomeBooleanPreparedSpec P -∗
  zesuEncoderBooleanCallSpec.
Proof.
  iIntros "Hnext Hentry".
  iEval (unfold writeSuccessTransactionsPriorityFeeSomeBooleanPreparedSpec)
    in "Hentry".
  iDestruct "Hentry" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hsys & Htmp & Hcaller & Hsaved &
      H1 & H2 & H10 & H11 & Hstack & Hmmio & Htrace & Hframe & %Halign &
      %Hlower & %Hupper & _)".
  iPoseProof
    (write_success_transactions_priority_fee_some_boolean_return_pre P sp
      base transaction transactions processed remaining bytes prefix suffix
      tail with "Hnext Hframe") as "Hret".
  iAssert (writeSuccessTransactionsPriorityFeeSomeBooleanRegisters
      transaction sp)%I
    with "[Hsys Htmp H10 H11 Hcaller Hsaved H1 H2]" as "Hregs".
  { rewrite /writeSuccessTransactionsPriorityFeeSomeBooleanRegisters.
    iFrame "Hsys Htmp H10 H11 Hcaller Hsaved H1 H2". }
  iPoseProof
    (write_success_transactions_priority_fee_some_boolean_abi_tail sp
      transaction remaining tail Halign Hlower Hupper
      with "Hstack Hmmio Htrace Hret") as "Htail".
  iPoseProof
    (write_success_transactions_priority_fee_some_boolean_registers transaction
      sp (writeSuccessTransactionsPriorityFeeSomeBooleanAbiTail
        sp transaction remaining tail)
      with "[Hregs Htail]") as "Habi".
  { iFrame. }
  iApply
    (write_success_transactions_priority_fee_some_boolean_abi_finalize
      transaction remaining sp tail with "Habi").
Qed.
