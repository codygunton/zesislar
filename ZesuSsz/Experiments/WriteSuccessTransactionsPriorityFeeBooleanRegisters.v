Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeNoneBoundary.

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
    `{!islaG Sigma} `{!threadG} (sp ret : bv 64) (R : iProp Sigma) : iProp Sigma :=
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
  "x8" ↦ᵣ: fun r8 => ⌜valu_has_shape r8 (BitsShape 64)⌝ ∗
  "x9" ↦ᵣ: fun r9 => ⌜valu_has_shape r9 (BitsShape 64)⌝ ∗
  "x18" ↦ᵣ: fun r18 => ⌜valu_has_shape r18 (BitsShape 64)⌝ ∗
  "x19" ↦ᵣ: fun r19 => ⌜valu_has_shape r19 (BitsShape 64)⌝ ∗
  "x20" ↦ᵣ: fun r20 => ⌜valu_has_shape r20 (BitsShape 64)⌝ ∗
  "x21" ↦ᵣ: fun r21 => ⌜valu_has_shape r21 (BitsShape 64)⌝ ∗
  "x22" ↦ᵣ: fun r22 => ⌜valu_has_shape r22 (BitsShape 64)⌝ ∗
  "x23" ↦ᵣ: fun r23 => ⌜valu_has_shape r23 (BitsShape 64)⌝ ∗
  "x24" ↦ᵣ: fun r24 => ⌜valu_has_shape r24 (BitsShape 64)⌝ ∗
  "x25" ↦ᵣ: fun r25 => ⌜valu_has_shape r25 (BitsShape 64)⌝ ∗
  "x26" ↦ᵣ: fun r26 => ⌜valu_has_shape r26 (BitsShape 64)⌝ ∗
  "x27" ↦ᵣ: fun r27 => ⌜valu_has_shape r27 (BitsShape 64)⌝ ∗
  "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗ R)%I.

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeBooleanAbiRegisters.

Lemma write_success_transactions_priority_fee_boolean_registers
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp ret : bv 64) (R : iProp Sigma) :
  writeSuccessTransactionsPriorityFeeBooleanRegisters transaction sp ret ∗ R -∗
  writeSuccessTransactionsPriorityFeeBooleanAbiRegisters sp ret R.
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
  iEval (rewrite /writeSuccessTransactionsPriorityFeeSavedShapes /reg_col /=)
    in "Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)". subst v8.
  iDestruct "H9" as (v9) "(%Hv9 & H9)". subst v9.
  iDestruct "H18" as (v18) "(%Hv18 & H18)". subst v18.
  iDestruct "H19" as (v19) "(%Hv19 & H19)". subst v19.
  iDestruct "H20" as (v20) "(%Hv20 & H20)". subst v20.
  iDestruct "H21" as (v21) "(%Hv21 & H21)". subst v21.
  iDestruct "H22" as (v22) "(%Hv22 & H22)". subst v22.
  iDestruct "H23" as (v23) "(%Hv23 & H23)". subst v23.
  iDestruct "H24" as (v24) "(%Hv24 & H24)". subst v24.
  iDestruct "H25" as (v25) "(%Hv25 & H25)". subst v25.
  iDestruct "H26" as (v26) "(%Hv26 & H26)". subst v26.
  iDestruct "H27" as (v27) "(%Hv27 & H27)". subst v27.
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
  iFrame "H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 HR".
  repeat iSplit; try iPureIntro; try reflexivity; try done.
Qed.
