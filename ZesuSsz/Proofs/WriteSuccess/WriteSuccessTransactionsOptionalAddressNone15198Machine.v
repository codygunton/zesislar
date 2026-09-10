From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.

Lemma write_success_transactions_optional_address_none_15198_machine
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction)
    (Hto : writeSuccessTransactionTo transaction = None)
    :
  reg_col zesu_ram_sys_regs -∗
  reg_col writeSuccessTransactions150e8OtherRegShapes -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x1" ↦ᵣ v)%I -∗
  "x2" ↦ᵣ RVal_Bits sp -∗
  "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x6" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x7" ↦ᵣ v)%I -∗
  reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] -∗
  "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) -∗
  "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x12" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x13" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x14" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x15" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x16" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x17" ↦ᵣ v)%I -∗
  "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) -∗
  "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) -∗
  "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) -∗
  "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) -∗
  "x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) -∗
  "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) -∗
  "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) -∗
  "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) -∗
  "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) -∗
  "x27" ↦ᵣ RVal_Bits
    (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x28" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x29" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x30" ↦ᵣ v)%I -∗
  (∃ v : valu, ⌜valu_has_shape v (BitsShape 64)⌝ ∗ "x31" ↦ᵣ v)%I -∗
  writeSuccessTransactionsScratch150e8
    sp base transactions processed transaction -∗
  writeSuccessTransactionsMachine1519c
    sp base transactions processed transaction.
Proof.
  iStartProof.
  iIntros "Hsys Hother H1 H2 H5 H6 H7 H10_11 H8 H9 H12 H13 H14 H15 H16
    H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 Hscratch".
  iEval (rewrite !reg_col_cons reg_col_nil) in "H10_11".
  iDestruct "H10_11" as "(H10 & H11 & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as "(H3 & H4 & _)".
  iAssert (writeSuccessTransactionsScratch1519c
      sp base transactions processed transaction)%I
    with "[Hscratch]" as "Hscratch1519c".
  { iEval (unfold writeSuccessTransactionsScratch150e8) in "Hscratch".
    iDestruct "Hscratch" as
      "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 &
        Hs10 & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs16 & Hs17 & Hs18 &
        Hs19 & Hs20 & Hs21 & Hs22 & Hs23 & Hs24 & Hs25 & Hs26 & Hs27 &
        Hs28 & Hs29 & Hs30 & Hs31 & Hs32 & _)".
    rewrite /writeSuccessTransactionsScratch1519c Hto.
    iFrame. }
  iEval (unfold writeSuccessTransactionsMachine1519c).
  rewrite /writeSuccessTransactions1519cOtherRegShapes
    /writeSuccessTransactions1519cOtherRegisters.
  cbn [writeSuccessTransactions1519cOtherRegShapes
    writeSuccessTransactions1519cOtherRegisters].
  rewrite !reg_col_cons reg_col_nil.
  iFrame.
Qed.
