From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_87 Require Import a15674_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15670Events.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Call.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15678.

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
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))) ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674CallEntryEventsSpec) := I.

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
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail), first, second,
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
