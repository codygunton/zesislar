Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanRegisters.

Definition writeSuccessTransactionsPriorityFeeSomeBooleanRegisters
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction)
    (sp : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
   "x10" ↦ᵣ RVal_Bits (BV 64 1) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
   reg_col writeSuccessTransactionsPriorityFeeCallerShapes ∗
   reg_col (writeSuccessTransactionsPriorityFeeSavedShapes transaction) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15128) ∗
   "x2" ↦ᵣ RVal_Bits sp)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeSomeBooleanRegisters) := I.

Lemma write_success_transactions_priority_fee_some_boolean_registers
    `{!islaG Sigma} `{!threadG} (transaction : writeSuccessTransaction)
    (sp : bv 64) (R : iProp Sigma) :
  writeSuccessTransactionsPriorityFeeSomeBooleanRegisters transaction sp ∗ R -∗
  writeSuccessTransactionsPriorityFeeBooleanAbiRegisters transaction sp
    (BV 64 0x15128) R.
Proof.
  iIntros "[Hregs HR]".
  rewrite /writeSuccessTransactionsPriorityFeeBooleanAbiRegisters.
  iEval (unfold writeSuccessTransactionsPriorityFeeSomeBooleanRegisters)
    in "Hregs".
  iDestruct "Hregs" as
    "(Hsys & Htmp & H10 & H11 & Hcaller & Hsaved & H1 & H2)".
  iEval (rewrite /writeSuccessTransactionsPriorityFeeCallerShapes /reg_col /=)
    in "Hcaller".
  iDestruct "Hcaller" as
    "(H12 & H13 & H14 & H15 & H16 & H17 & _)".
  iDestruct "H12" as (v12) "(%Hv12 & H12)".
  destruct (valu_has_bits_shape v12 64 Hv12) as (b12 & ->).
  iDestruct "H13" as (v13) "(%Hv13 & H13)".
  destruct (valu_has_bits_shape v13 64 Hv13) as (b13 & ->).
  iDestruct "H14" as (v14) "(%Hv14 & H14)".
  destruct (valu_has_bits_shape v14 64 Hv14) as (b14 & ->).
  iDestruct "H15" as (v15) "(%Hv15 & H15)".
  destruct (valu_has_bits_shape v15 64 Hv15) as (b15 & ->).
  iDestruct "H16" as (v16) "(%Hv16 & H16)".
  destruct (valu_has_bits_shape v16 64 Hv16) as (b16 & ->).
  iDestruct "H17" as (v17) "(%Hv17 & H17)".
  destruct (valu_has_bits_shape v17 64 Hv17) as (b17 & ->).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp H10 H11 H12 H13 H14 H15 H16 H17 H1 H2".
  iExists (BV 64 1). iSplit; first done.
  iExists (BV 64 16). iSplit; first done.
  iExists b12. iSplit; first done.
  iExists b13. iSplit; first done.
  iExists b14. iSplit; first done.
  iExists b15. iSplit; first done.
  iExists b16. iSplit; first done.
  iExists b17. iSplit; first done.
  iFrame "Hsaved HR".
Qed.
