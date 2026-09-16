Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674DataCallJalrStrong.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674SavedShapes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalTailState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsPost15678WithdrawalsTotalData
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (withdrawalBase : Z) (count : nat)
    (bytes : list (bv 8)) (tail : spec)
    (preserved : iProp Sigma) : iProp Sigma :=
  (bv_unsigned pointer ↦ₘ∗ bytes ∗
   ⌜bv_unsigned pointer = withdrawalBase⌝ ∗
   ⌜length bytes = (48 * count)%nat⌝ ∗
   ⌜(count < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜(mapRamBase defaultMap) <= withdrawalBase⌝ ∗
   ⌜withdrawalBase + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   instr_pre 0x156e8
     (writeSuccessWithdrawalsLoopExit sp withdrawalBase count bytes tail
       (preserved ∗ P)) ∗
   P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15678WithdrawalsTotalData) := I.

Lemma write_success_transactions_post_15678_withdrawals_total_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp first second pointer : bv 64)
    (transactionBase withdrawalBase : Z) (transactionTotal count : nat)
    (items : list ByteListItem) (bytes : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsPost15674DataCallReturnFixedSpec
    (writeSuccessTransactionsPost15678WithdrawalsTotalData P sp pointer
      withdrawalBase count bytes tail
      (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
        transactionTotal first second items))
    sp transactionBase transactionTotal
    (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessWithdrawalsEvents sp count tail))
    first second pointer (Z_to_bv 64 (Z.of_nat count)) items -∗
  writeSuccessTransactionsWithdrawalsTotalAt15678Spec
    (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
      transactionTotal first second items ∗ P).
Proof.
  iStartProof. iIntros "Hreturn".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallReturnFixedSpec)
    in "Hreturn".
  iDestruct "Hreturn" as (saved r10 r11)
    "(Hsys & Hcaller & Hsaved & %HsavedLength & %HsavedShapes & HreturnOther &
      H2 & H10 & H11 & Hscratch & Hcarrier & HupperScratch & Hmmio & Htrace &
      Hdata & _)".
  iPoseProof (write_success_transactions_post_15674_saved_shapes saved with
    "Hsaved [] []") as "HsavedBits".
  { iPureIntro. exact HsavedLength. }
  { iPureIntro. exact HsavedShapes. }
  iEval (unfold writeSuccessTransactionsPost15674Caller; cbn) in "Hcaller".
  iDestruct "Hcaller" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iEval (unfold writeSuccessTransactionsPost15674Saved; cbn) in "HsavedBits".
  iDestruct "HsavedBits" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iEval (unfold writeSuccessTransactionsPost15674ReturnOther; cbn)
    in "HreturnOther".
  iDestruct "HreturnOther" as "(H3 & H4 & _)".
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    writeSuccessTransactionsWithdrawalsPreservedRegisters))%I
    with "[H3 H4 H6 H7 H12 H13 H14 H15 H16 H17 H19 H20 H21 H22 H23 H24
      H25 H26 H27 H28 H29 H30 H31]" as "HpreservedRegisters".
  { iEval (unfold writeSuccessTransactionsWithdrawalsPreservedRegisters; cbn).
    iFrame. }
  iDestruct "H1" as (v1) "(%Hv1 & H1)".
  iDestruct "H5" as (v5) "(%Hv5 & H5)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)".
  iDestruct "H9" as (v9) "(%Hv9 & H9)".
  iDestruct "H18" as (v18) "(%Hv18 & H18)".
  iAssert ("x1" ↦ᵣ: (fun _ => True))%I with "[H1]" as "H1Any".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists v1. iFrame. }
  iAssert ("x5" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H5]" as "H5Bits".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists v5. iFrame. iPureIntro. exact Hv5. }
  iAssert ("x8" ↦ᵣ: (fun _ => True))%I with "[H8]" as "H8Any".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists v8. iFrame. }
  iAssert ("x9" ↦ᵣ: (fun _ => True))%I with "[H9]" as "H9Any".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists v9. iFrame. }
  iAssert ("x10" ↦ᵣ: (fun _ => True))%I with "[H10]" as "H10Any".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists (RVal_Bits r10). iFrame. }
  iAssert ("x11" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H11]" as "H11Bits".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists (RVal_Bits r11). iFrame. done. }
  iAssert ("x18" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H18]" as "H18Bits".
  { iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
    iExists v18. iFrame. iPureIntro. exact Hv18. }
  iEval (rewrite /writeSuccessTransactionsPuncturedScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & HtransactionBase & HtransactionTotal & Hprefix & Hmiddle & Htail & _)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hlower") as
    "(Hlower32 & HlowerRest)"; first lia.
  have HlowerRestAddress : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
  iEval (rewrite HlowerRestAddress) in "HlowerRest".
  iDestruct (mem_mapsto_uninit_split 16 with "HlowerRest") as
    "(HcallScratch & Hlower104)"; first lia.
  have Hlower104Address : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
  iEval (rewrite Hlower104Address) in "Hlower104".
  iEval (rewrite /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier) in "Hcarrier".
  iDestruct "Hcarrier" as
    "((Hfirst & Hsecond & HpointerWord & HcountWord) & HcallStack & Hitems &
      HitemFacts)".
  iAssert (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
    transactionTotal first second items)%I
    with "[HcallStack Hlower32 Hlower104 HtransactionBase HtransactionTotal
      Hprefix Hfirst Hsecond Hmiddle Htail Hitems HitemFacts]" as "Hpreserved".
  { iEval (rewrite /writeSuccessTransactionsPost15678PreservedScratch).
    iFrame. }
  iEval (rewrite /writeSuccessTransactionsPost15678WithdrawalsTotalData)
    in "Hdata".
  iDestruct "Hdata" as
    "(Hbytes & %Hpointer & %Hlength & %Hcount & %Halign & %HlowerBound &
      %HupperBound & %HbaseLower & %HbaseUpper & Hexit & HP & _)".
  iAssert (writeSuccessTransactionsWithdrawalsTotalResources
    (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
      transactionTotal first second items ∗ P)
    sp pointer withdrawalBase count bytes tail)%I
    with "[Hbytes Hexit Hpreserved HP]" as "Hresources".
  { iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalResources).
    iFrame. repeat iSplit; iPureIntro; assumption. }
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt15678Spec).
  iExists sp, pointer, withdrawalBase, count, bytes, tail.
  iFrame "Hsys H2 H8Any H9Any".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalTailFrame).
  iFrame "HpreservedRegisters H1Any H5Bits H10Any H11Bits H18Bits HcallScratch
    HpointerWord HcountWord HupperScratch Hmmio Htrace Hresources".
  repeat iSplit; iPureIntro; assumption.
Qed.
