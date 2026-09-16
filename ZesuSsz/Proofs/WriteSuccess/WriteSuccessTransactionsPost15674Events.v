Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_87 Require Import a15674_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15670Events.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15678.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15670Events.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668Events.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566cEvents.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessTransactionsPost15674CallEntryEventsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem) (saved : list valu),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674CallRegisters) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost15674Saved saved) ∗ ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun v => valu_has_shape v (BitsShape 64)) saved⌝ ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits first ∗ "x11" ↦ᵣ RVal_Bits second ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    (bv_unsigned sp) ↦ₘ? 104 ∗
    (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
    (bv_unsigned sp + 120) ↦ₘ? 984 ∗ (bv_unsigned sp + 1104) ↦ₘ first ∗
    (bv_unsigned sp + 1112) ↦ₘ second ∗ (bv_unsigned sp + 1120) ↦ₘ? 776 ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))) ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674CallEntryEventsSpec) := I.

Lemma write_success_transactions_post_15674_events_entry_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsPostAt15674EventsSpec P -∗
  writeSuccessTransactionsPost15674CallEntryEventsSpec P.
Proof.
  iStartProof. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt15674EventsSpec) in "Hentry".
  iDestruct "Hentry" as (sp base transactions bytes tail first second items)
    "(Hsys & H1 & Hother & H2 & H10 & H11 & Hbase & Hown & HscratchLower &
      HbaseWord & HlengthWord & HscratchPrefix & HscratchFirst & HscratchSecond &
      HscratchSuffix & Hitems & %Hfacts & Hmmio & Htrace &
      (Hq & _))".
  iDestruct "Hq" as "(HcallStack & %HspAlign16 & %HspAlign8 &
    %HspLower & %HspUpper & HP)".
  destruct Hfacts as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
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
  iDestruct (mem_mapsto_uninit_split 48 with "HscratchLower") as
    "(Hstack48 & HlowerFrame)"; first lia.
  have HlowerFrameAddress : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
  iEval (rewrite HlowerFrameAddress) in "HlowerFrame".
  iAssert ((bv_unsigned sp - 80) ↦ₘ? 80)%I
    with "[HcallStack Hstack48]" as "HcallStack80".
  { iApply (@mem_mapsto_uninit_combine _ _ 32 _ _ 80 with "HcallStack"); first lia.
    have HstackAddress : bv_unsigned sp - 80 + 32 = bv_unsigned sp - 48 by lia.
    iEval (rewrite -HstackAddress) in "Hstack48".
    iExact "Hstack48". }
  iEval (rewrite /writeSuccessTransactionsPost15674CallEntryEventsSpec).
  iExists sp, base, transactions, bytes, tail, first, second, items,
    [RVal_Bits a8; RVal_Bits a9; RVal_Bits a18; RVal_Bits a19; RVal_Bits a20;
     RVal_Bits a21; RVal_Bits a22; RVal_Bits a23; RVal_Bits a24; RVal_Bits a25;
     RVal_Bits a26; RVal_Bits a27].
  iEval (unfold writeSuccessTransactionsPost15674CallRegisters;
    unfold writeSuccessTransactionsPost15674Saved;
    unfold writeSuccessTransactionsPost15674ReturnOther; cbn).
  iSplitL "Hsys"; [iExact "Hsys"|].
  iFrame "H12 H13 H14 H15 H16 H17 H5 H6 H7 H28 H29 H30 H31
    H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H3 H4 H1 H2 H10 H11
    HcallStack80 HlowerFrame HbaseWord HlengthWord HscratchPrefix HscratchFirst
    HscratchSecond HscratchSuffix Hbase Hown Hitems Hmmio Htrace HP".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  all: try reflexivity.
  all: try (repeat constructor; cbn; exact inhabitant).
Qed.

Lemma write_success_transactions_post_15674_events_entry_to_raw
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsPost15674CallEntryEventsSpec P -∗
  writeSuccessTransactionsPost15674CallEntrySpec P.
Proof.
  iStartProof. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost15674CallEntryEventsSpec) in "Hentry".
  iDestruct "Hentry" as (sp base transactions bytes tail first second items saved)
    "(Hsys & Hcaller & Hsaved & HsavedLength & HsavedShapes & HreturnOther & H1 & H2 & H10 & H11 &
      HcallStack & HlowerFrame & HbaseWord & HlengthWord & HscratchPrefix & HscratchFirst &
      HscratchSecond & HscratchSuffix & Hbase & Hown & Hitems & Hfacts & HspUpper & Hmmio &
      Htrace & HP & _)".
  iEval (rewrite /writeSuccessTransactionsPost15674CallEntrySpec).
  iExists sp, base, transactions, bytes,
    (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail), first, second,
    items, saved.
  iFrame.
Qed.

Lemma write_success_transactions_post_15674_events
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x15678 (writeSuccessTransactionsPost15678Spec P) -∗
  instr_body 0x15674 (writeSuccessTransactionsPost15674CallEntryEventsSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hcallee Hnext".
  iPoseProof (write_success_transactions_post_15674_call P with
    "Hlookup Hcode Hcallee Hnext") as "Hraw".
  iApply (instr_pre_wand 0x15674 0x15674 false false with "Hraw");
    [done | done |].
  iIntros "Hentry".
  iApply (write_success_transactions_post_15674_events_entry_to_raw P with "Hentry").
Qed.

Lemma write_success_transactions_post_15674_events_to_15678
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x1567c (writeSuccessTransactionsPostAt1567cSpec P) -∗
  instr_body 0x15674 (writeSuccessTransactionsPost15674CallEntryEventsSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hcallee Hpost1567c".
  iApply (write_success_transactions_post_15674_events P with
    "Hlookup Hcode Hcallee").
  iApply (write_success_transactions_post_15678_load P with
    "Hlookup Hpost1567c").
Qed.

Lemma write_success_transactions_post_15674_events_from_post
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x1567c (writeSuccessTransactionsPostAt1567cSpec P) -∗
  instr_body 0x15674 (writeSuccessTransactionsPostAt15674EventsSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hcallee Hpost1567c".
  iPoseProof (write_success_transactions_post_15674_events_to_15678 P with
    "Hlookup Hcode Hcallee Hpost1567c") as "Hcall".
  iApply (instr_pre_wand 0x15674 0x15674 false false with "Hcall");
    [done | done |].
  iIntros "Hentry".
  iApply (write_success_transactions_post_15674_events_entry_adapter P with "Hentry").
Qed.

Lemma write_success_transactions_post_15668_events_to_1567c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x1567c (writeSuccessTransactionsPostAt1567cSpec P) -∗
  instr_body 0x15668 (writeSuccessTransactionsPostAt15668EventsSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hcallee Hpost1567c".
  iApply (write_success_transactions_post_15668_events P with "Hlookup Hcode").
  iApply (write_success_transactions_post_1566c_events P with "Hlookup").
  iApply (write_success_transactions_post_15670_events P with "Hlookup").
  iApply (write_success_transactions_post_15674_events_from_post P with
    "Hlookup Hcode Hcallee Hpost1567c").
Qed.
