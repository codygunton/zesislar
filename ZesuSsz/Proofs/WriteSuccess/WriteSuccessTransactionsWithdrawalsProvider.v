Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1568cWithdrawals.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsPayload.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Import ListNotations.

Definition writeSuccessTransactionsWithdrawalsPreservedRegisters :
    list string :=
  ["x3"; "x4"; "x6"; "x7";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
   "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactionsWithdrawalsIntEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsWithdrawalsPreservedRegisters) ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 0x1568c) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x11" ↦ᵣ: (fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
    "x18" ↦ᵣ: (fun r18 => ⌜valu_has_shape r18 (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessWithdrawalsEvents sp (S remaining) tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    writeSuccessTransactionsWithdrawalsPayload P sp pointer base total processed
      remaining bytes prefix suffix tail ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsIntEntrySpec) := I.

Lemma write_success_transactions_withdrawals_int_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x1568c (writeSuccessTransactionsPost1568cWithdrawalsSpec P) -∗
  instr_body 0x15d10 (writeSuccessTransactionsWithdrawalsIntEntrySpec P).
Proof.
  iStartProof. iIntros "Hint Hreturn".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsIntEntrySpec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes prefix suffix tail)
    "(Hsys & Hpreserved & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 &
      HcallScratch & Hmmio & Htrace & %Halign & %Hlower & %Hupper & Hpayload & _)".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsPayload) in "Hpayload".
  iDestruct "Hpayload" as
    "(HpointerWord & HcountWord & HupperScratch & Hprefix & Hsuffix & Hinv &
      Hexit & HP & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (r5) "(H5 & %Hr5)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H11" as (r11) "(H11 & %Hr11)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H18".
  iDestruct "H18" as (r18) "(H18 & %Hr18)".
  iEval (rewrite /zesuEncoderIntCallSpec).
  iApply "Hint".
  iExists (Z_to_bv 64 (Z.of_nat (S remaining))), sp, 0x1568c,
    (writeSuccessWithdrawalsEvents sp (S remaining) tail).
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
  iEval (rewrite /writeSuccessTransactionsPost1568cWithdrawalsSpec).
  iExists sp.
  iSplitL "Hsys"; first iExact "Hsys".
  iSplitL "H2"; first iExact "H2".
  iSplitL "H18".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists r18. iFrame "H18". }
  iEval (rewrite /writeSuccessTransactionsPost1568cWithdrawalsRest
    /writeSuccessWithdrawalsScratch).
  iExists pointer, base, total, processed, remaining, bytes, prefix, suffix, tail.
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
  iEval (rewrite instr_pre'_eq).
  iFrame "Hother H8 H9 Hprefix Hsuffix
    HupperScratch HcallScratch Hmmio Htrace HP Hinv Hexit".
Qed.
