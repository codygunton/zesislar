Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.

Definition writeSuccessTransactionsPriorityFeeBooleanRegisters
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp ret : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
   "x10" ↦ᵣ RVal_Bits (BV 64 0) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
   reg_col writeSuccessTransactionsPriorityFeeCallerShapes ∗
   reg_col (writeSuccessTransactionsPriorityFeeSavedShapes transaction) ∗
   "x1" ↦ᵣ RVal_Bits ret ∗
   "x2" ↦ᵣ RVal_Bits sp)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeBooleanRegisters) := I.

Definition writeSuccessTransactionsPriorityFeeBooleanAbiRegisters
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp ret : bv 64) (R : iProp Sigma) : iProp Sigma :=
  (
  reg_col zesu_ram_sys_regs ∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
  "x10" ↦ᵣ: fun r10 => ∃ b10 : bv 64, ⌜r10 = RVal_Bits b10⌝ ∗
  "x11" ↦ᵣ: fun r11 => ∃ b11 : bv 64, ⌜r11 = RVal_Bits b11⌝ ∗
  "x12" ↦ᵣ: fun r12 => ∃ b12 : bv 64, ⌜r12 = RVal_Bits b12⌝ ∗
  "x13" ↦ᵣ: fun r13 => ∃ b13 : bv 64, ⌜r13 = RVal_Bits b13⌝ ∗
  "x14" ↦ᵣ: fun r14 => ∃ b14 : bv 64, ⌜r14 = RVal_Bits b14⌝ ∗
  "x15" ↦ᵣ: fun r15 => ∃ b15 : bv 64, ⌜r15 = RVal_Bits b15⌝ ∗
  "x16" ↦ᵣ: fun r16 => ∃ b16 : bv 64, ⌜r16 = RVal_Bits b16⌝ ∗
  "x17" ↦ᵣ: fun r17 => ∃ b17 : bv 64, ⌜r17 = RVal_Bits b17⌝ ∗
  reg_col (writeSuccessTransactionsPriorityFeeSavedShapes transaction) ∗
  "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗ R)%I.

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeBooleanAbiRegisters.

Lemma write_success_transactions_priority_fee_boolean_registers
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp ret : bv 64) (R : iProp Sigma) :
  writeSuccessTransactionsPriorityFeeBooleanRegisters transaction sp ret ∗ R -∗
  writeSuccessTransactionsPriorityFeeBooleanAbiRegisters transaction sp ret R.
Proof.
  iStartProof. iIntros "[Hregs HR]".
  rewrite /writeSuccessTransactionsPriorityFeeBooleanAbiRegisters.
  iEval (unfold writeSuccessTransactionsPriorityFeeBooleanRegisters) in "Hregs".
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
  iExists (BV 64 0). iSplit; first done.
  iExists (BV 64 16). iSplit; first done.
  iExists b12. iSplit; first done.
  iExists b13. iSplit; first done.
  iExists b14. iSplit; first done.
  iExists b15. iSplit; first done.
  iExists b16. iSplit; first done.
  iExists b17. iSplit; first done.
  iFrame "Hsaved HR".
Qed.
