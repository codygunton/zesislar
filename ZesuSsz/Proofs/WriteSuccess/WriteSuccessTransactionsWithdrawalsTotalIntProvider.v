From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalTailState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsWithdrawalsTotalIntEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (count : nat)
      (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsWithdrawalsPreservedRegisters) ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 0x1568c) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat count)) ∗
    "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat count)) ∗
    "x11" ↦ᵣ: (fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
    "x18" ↦ᵣ: (fun r18 => ⌜valu_has_shape r18 (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1120) ↦ₘ pointer ∗
    (bv_unsigned sp + 1128) ↦ₘ Z_to_bv 64 (Z.of_nat count) ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessWithdrawalsEvents sp count tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    writeSuccessTransactionsWithdrawalsTotalResources P sp pointer base count
      bytes tail ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalIntEntrySpec) := I.

Lemma write_success_transactions_withdrawals_total_int_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x1568c
    (writeSuccessTransactionsWithdrawalsTotalAt1568cSpec P) -∗
  instr_body 0x15d10
    (writeSuccessTransactionsWithdrawalsTotalIntEntrySpec P).
Proof.
  iStartProof. iIntros "Hint Hreturn".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalIntEntrySpec) in "Hentry".
  iDestruct "Hentry" as (sp pointer base count bytes tail)
    "(Hsys & Hpreserved & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 &
      HcallScratch & HpointerWord & HcountWord & HupperScratch & Hmmio & Htrace &
      %Halign & %Hlower & %Hupper & Hresources & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (r5) "(H5 & %Hr5)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H11" as (r11) "(H11 & %Hr11)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H18".
  iDestruct "H18" as (r18) "(H18 & %Hr18)".
  iEval (rewrite /zesuEncoderIntCallSpec).
  iApply "Hint".
  iExists (Z_to_bv 64 (Z.of_nat count)), sp, 0x1568c,
    (writeSuccessWithdrawalsEvents sp count tail).
  iFrame "Hsys H1 H2".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iExists r5. iFrame "H5". iSplit; first (iPureIntro; exact Hr5).
  iSplitL "H10"; first iExact "H10".
  iExists r11. iFrame "H11". iSplit; first (iPureIntro; exact Hr11).
  iFrame "HcallScratch Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & HcallScratch & Hmmio & Htrace & _)".
  iApply "Hreturn".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt1568cSpec).
  iExists sp, pointer, base, count, bytes, tail.
  iSplitL "Hsys"; first iExact "Hsys".
  iSplitL "H2"; first iExact "H2".
  iSplitL "H18".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists r18. iFrame "H18". }
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt1568cRest
    /writeSuccessWithdrawalsScratch).
  iEval (unfold writeSuccessTransactionsWithdrawalsPreservedRegisters;
    unfold writeSuccessWithdrawalsOtherRegShapes,
      writeSuccessWithdrawalsOtherRegisters; cbn) in "Hpreserved".
  iDestruct "Hpreserved" as
    "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 & H19 & H20 &
      H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & _)".
  iAssert (reg_col writeSuccessWithdrawalsOtherRegShapes)%I
    with "[H1 H3 H4 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H19 H20 H21
      H22 H23 H24 H25 H26 H27 H28 H29 H30 H31]" as "Hother".
  { iEval (unfold writeSuccessWithdrawalsOtherRegShapes,
      writeSuccessWithdrawalsOtherRegisters; cbn).
    iFrame. done. }
  iFrame "Hother H8 H9 HupperScratch HcallScratch Hmmio Htrace Hresources".
Qed.
