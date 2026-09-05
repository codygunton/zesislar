From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668DataStates.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674DataCallJalr.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessTransactionsPost15678DataSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transactions : list writeSuccessTransaction) (bytes : list (bv 8)),
    writeSuccessTransactionsPost15674DataCallReturnSpec
      (base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
       ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
       ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
       ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15678DataSpec) := I.

Lemma write_success_transactions_post_15674_data
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x15678 (writeSuccessTransactionsPost15678DataSpec P) -∗
  instr_body 0x15674 (writeSuccessTransactionsPost15674DataSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hcallee Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost15674DataSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base transactions bytes tail remaining first second items)
    "(Hsys & H1 & Hother & H2 & H10 & H11 & Hbase & Hown & Hscratch &
      Hcarrier & Hwithdrawals & Hmmio & Htrace & %Halign16 & %Halign8 &
      %Hlow & %Hhigh & HP & _)".
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
  set (F := (base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I).
  iEval (rewrite -instr_pre'_eq) in "Hcallee".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_post_15674_data_call_jalr F with
    "Hlookup Hcode Hcallee") as "Hjalr".
  iSpecialize ("Hjalr" with "[Hnext]").
  { iApply (instr_pre_wand 0x15678 0x15678 false false with "Hnext");
      [done | done |].
    iIntros "Hreturn".
    iEval (rewrite /writeSuccessTransactionsPost15678DataSpec).
    iExists sp, base, transactions, bytes.
    iEval (rewrite /F) in "Hreturn". iExact "Hreturn". }
  iEval (rewrite instr_pre'_eq) in "Hjalr". iApply "Hjalr".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallEntrySpec).
  iExists sp, base, (length transactions),
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail), first, second,
    pointer, (Z_to_bv 64 (Z.of_nat (S remaining))), items,
    [RVal_Bits a8; RVal_Bits a9; RVal_Bits a18; RVal_Bits a19; RVal_Bits a20;
     RVal_Bits a21; RVal_Bits a22; RVal_Bits a23; RVal_Bits a24; RVal_Bits a25;
     RVal_Bits a26; RVal_Bits a27].
  iEval (unfold writeSuccessTransactionsPost15674CallRegisters;
    unfold writeSuccessTransactionsPost15674Saved;
    unfold writeSuccessTransactionsPost15674ReturnOther; cbn).
  iSplitL "Hsys"; [iExact "Hsys"|].
  iFrame "H12 H13 H14 H15 H16 H17 H5 H6 H7 H28 H29 H30 H31
    H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H3 H4 H1 H2 H10 H11
    Hscratch Hcarrier Hwithdrawals Hmmio Htrace Hbase Hown HP".
  repeat iSplit; try iPureIntro; try assumption; try reflexivity; try done.
  repeat constructor; cbn; exact inhabitant.
Qed.
