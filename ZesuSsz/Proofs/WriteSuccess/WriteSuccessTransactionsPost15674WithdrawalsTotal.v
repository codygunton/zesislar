Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668DataStates.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674DataCallJalrStrong.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15678WithdrawalsTotal.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15678WithdrawalsTotalAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsCarrierWithdrawalsTotalData
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (bv_unsigned pointer ↦ₘ∗ withdrawalBytes ∗
   ⌜bv_unsigned pointer = withdrawalBase⌝ ∗
   ⌜length withdrawalBytes = (48 * count)%nat⌝ ∗
   ⌜(count < 2 ^ 64)%nat⌝ ∗
   ⌜(mapRamBase defaultMap) <= withdrawalBase⌝ ∗
   ⌜withdrawalBase + Z.of_nat (length withdrawalBytes) < (machineRamEnd defaultMap)⌝ ∗
   instr_pre 0x156e8
     (writeSuccessWithdrawalsLoopExit sp withdrawalBase count withdrawalBytes tail
       (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
          (length transactions) first second items ∗
        transactionBase ↦ₘ∗ transactionBytes ∗
        writeSuccessTransactionsOwn transactions ∗ P)) ∗
   P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsCarrierWithdrawalsTotalData) := I.

Definition writeSuccessTransactionsPost15674WithdrawalsTotalSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗
   reg_col writeSuccessTransactionsPostOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
   "x11" ↦ᵣ RVal_Bits second ∗
   transactionBase ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsPuncturedScratch sp transactionBase
     (length transactions) ∗
   writeSuccessTransactionsLoopCarrierPayload sp first second pointer
     (Z_to_bv 64 (Z.of_nat count)) items ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
     (byteListItemEvents (sp - BV 64 32)%bv items
       (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
         (writeSuccessWithdrawalsEvents sp count tail)))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   writeSuccessTransactionsCarrierWithdrawalsTotalData P sp pointer
     transactionBase withdrawalBase transactions transactionBytes count
     withdrawalBytes tail first second items ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674WithdrawalsTotalSpec) := I.

Lemma write_success_transactions_lower_48_to_16 (sp : bv 64) :
  ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z ->
  ((mapRamBase defaultMap) <= bv_unsigned sp - 16)%Z.
Proof. lia. Qed.

Lemma write_success_transactions_post_15674_withdrawals_total
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15694
    (writeSuccessTransactionsPostWithdrawalsHandoff
      (writeSuccessTransactionsPost15678PreservedScratch sp transactionBase
         (length transactions) first second items ∗
       transactionBase ↦ₘ∗ transactionBytes ∗
       writeSuccessTransactionsOwn transactions ∗ P)) -∗
  instr_body 0x15674
    (writeSuccessTransactionsPost15674WithdrawalsTotalSpec P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #HbyteLists #Hint #Hloop".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost15674WithdrawalsTotalSpec)
    in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & H1 & Hother & H2 & H10 & H11 & HtransactionBytes & Hown &
      Hscratch & Hcarrier & HupperScratch & Hmmio & Htrace & %Halign16 &
      %Halign8 & %Hlow & %Hhigh & Hdata & _)".
  iEval (rewrite /writeSuccessTransactionsCarrierWithdrawalsTotalData) in "Hdata".
  iDestruct "Hdata" as
    "(HwithdrawalBytes & %Hpointer & %Hlength & %HcountBound & %HbaseLower &
      %HbaseUpper & Hexit & HP & _)".
  iEval (unfold writeSuccessTransactionsPostOtherRegShapes; cbn) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H5 & H6 & H7 & H8 & H9 & H12 & H13 & H14 & H15 & H16 & H17 &
      H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "H8" as (r8) "(%Hr8 & H8)".
  apply valu_has_bits_shape in Hr8 as (a8 & ->).
  iDestruct "H9" as (r9) "(%Hr9 & H9)".
  apply valu_has_bits_shape in Hr9 as (a9 & ->).
  iDestruct "H18" as (r18) "(%Hr18 & H18)".
  apply valu_has_bits_shape in Hr18 as (a18 & ->).
  iDestruct "H19" as (r19) "(%Hr19 & H19)".
  apply valu_has_bits_shape in Hr19 as (a19 & ->).
  iDestruct "H20" as (r20) "(%Hr20 & H20)".
  apply valu_has_bits_shape in Hr20 as (a20 & ->).
  iDestruct "H21" as (r21) "(%Hr21 & H21)".
  apply valu_has_bits_shape in Hr21 as (a21 & ->).
  iDestruct "H22" as (r22) "(%Hr22 & H22)".
  apply valu_has_bits_shape in Hr22 as (a22 & ->).
  iDestruct "H23" as (r23) "(%Hr23 & H23)".
  apply valu_has_bits_shape in Hr23 as (a23 & ->).
  iDestruct "H24" as (r24) "(%Hr24 & H24)".
  apply valu_has_bits_shape in Hr24 as (a24 & ->).
  iDestruct "H25" as (r25) "(%Hr25 & H25)".
  apply valu_has_bits_shape in Hr25 as (a25 & ->).
  iDestruct "H26" as (r26) "(%Hr26 & H26)".
  apply valu_has_bits_shape in Hr26 as (a26 & ->).
  iDestruct "H27" as (r27) "(%Hr27 & H27)".
  apply valu_has_bits_shape in Hr27 as (a27 & ->).
  set (Final := (transactionBase ↦ₘ∗ transactionBytes ∗
    writeSuccessTransactionsOwn transactions ∗ P)%I).
  set (Preserved := writeSuccessTransactionsPost15678PreservedScratch sp
    transactionBase (length transactions) first second items).
  set (Data := writeSuccessTransactionsPost15678WithdrawalsTotalData Final sp
    pointer withdrawalBase count withdrawalBytes tail Preserved).
  iAssert Data with
    "[HwithdrawalBytes Hexit HtransactionBytes Hown HP]" as "HfixedData".
  { iEval (rewrite /Data /Final /Preserved
      /writeSuccessTransactionsPost15678WithdrawalsTotalData).
    iFrame "HwithdrawalBytes".
    iSplit; first (iPureIntro; exact Hpointer).
    iSplit; first (iPureIntro; exact Hlength).
    iSplit; first (iPureIntro; exact HcountBound).
    iSplit; first (iPureIntro; exact Halign16).
    iSplit; first (iPureIntro;
      exact (write_success_transactions_lower_48_to_16 sp Hlow)).
    iSplit; first (iPureIntro; exact Hhigh).
    iSplit; first (iPureIntro; exact HbaseLower).
    iSplit; first (iPureIntro; exact HbaseUpper).
    iFrame "Hexit".
    iEval (rewrite /Final). iFrame "HtransactionBytes Hown HP". }
  iPoseProof (write_success_transactions_post_15678_withdrawals_total Final sp
    first second pointer transactionBase withdrawalBase (length transactions)
    count items withdrawalBytes tail with "Hlookup [Hint] [Hloop]") as "Hnext".
  { iEval (rewrite -instr_pre'_eq) in "Hint". iExact "Hint". }
  { iEval (rewrite -instr_pre'_eq) in "Hloop". iExact "Hloop". }
  iPoseProof (write_success_transactions_post_15674_data_call_jalr_strong Data
    sp transactionBase (length transactions)
    (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessWithdrawalsEvents sp count tail))
    first second pointer (Z_to_bv 64 (Z.of_nat count)) items with
    "Hlookup Hcode [HbyteLists] Hnext") as "Hjalr".
  { iEval (rewrite -instr_pre'_eq) in "HbyteLists". iExact "HbyteLists". }
  iEval (rewrite instr_pre'_eq) in "Hjalr". iApply "Hjalr".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallEntryFixedSpec).
  iExists [RVal_Bits a8; RVal_Bits a9; RVal_Bits a18; RVal_Bits a19;
    RVal_Bits a20; RVal_Bits a21; RVal_Bits a22; RVal_Bits a23;
    RVal_Bits a24; RVal_Bits a25; RVal_Bits a26; RVal_Bits a27].
  iSplitL "Hsys"; first iExact "Hsys".
  iEval (unfold writeSuccessTransactionsPost15674CallRegisters;
    unfold writeSuccessTransactionsPost15674Saved;
    unfold writeSuccessTransactionsPost15674ReturnOther; cbn).
  iFrame "H12 H13 H14 H15 H16 H17 H5 H6 H7 H28 H29 H30 H31
    H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H3 H4 H1 H2 H10 H11
    Hscratch Hcarrier HupperScratch Hmmio Htrace HfixedData".
  repeat iSplit; try iPureIntro; try reflexivity; try done.
  repeat constructor; cbn; exact inhabitant.
Qed.
