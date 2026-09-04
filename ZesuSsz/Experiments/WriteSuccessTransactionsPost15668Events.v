From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15668.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import IslaTraces.write_success_87.a15668_spec.

Definition writeSuccessTransactionsPostAt15668EventsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactionsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
    "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    (bv_unsigned sp - 48) ↦ₘ? 152 ∗
    (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
    (bv_unsigned sp + 120) ↦ₘ? 984 ∗
    (bv_unsigned sp + 1104) ↦ₘ first ∗
    (bv_unsigned sp + 1112) ↦ₘ second ∗
    (bv_unsigned sp + 1120) ↦ₘ? 776 ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
    ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
       ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
       ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
       ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
       ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P))%I.

Definition writeSuccessTransactionsPostAt1566cEventsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactionsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    (bv_unsigned sp - 48) ↦ₘ? 152 ∗
    (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
    (bv_unsigned sp + 120) ↦ₘ? 984 ∗
    (bv_unsigned sp + 1104) ↦ₘ first ∗
    (bv_unsigned sp + 1112) ↦ₘ second ∗
    (bv_unsigned sp + 1120) ↦ₘ? 776 ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
    ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
     ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
     ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
     ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15668EventsSpec) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt1566cEventsSpec) := I.

Lemma write_success_transactions_post_15668_events
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1566c (writeSuccessTransactionsPostAt1566cEventsSpec P) -∗
  instr_body 0x15668 (writeSuccessTransactionsPostAt15668EventsSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  iPoseProof "Hlookup" as "#Hlookup15668".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15668".
  iPoseProof ("Hlookup15668" $! 0x15668 with "[]") as "#Hinstr15668".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15668. done. }
  iPoseProof (IslaTraces.write_success_87.a15668_spec.a15668_spec
    0x15668 with "Hinstr15668") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt15668EventsSpec) in "Hentry".
  iDestruct "Hentry" as (sp base transactions bytes tail first second items)
    "(Hsys & Hother & H2 & H10 & H11 & Harray & Hown & HscratchLower &
      HscratchBase & HscratchLength & HscratchPrefix & HscratchFirst & HscratchSecond &
      HscratchSuffix & Hitems & %Hfacts & Hmmio & Htrace & HcallStack &
      %HspAlign16 & %HspAlign8 & %HspLower & %HspUpper & HP)".
  destruct Hfacts as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
  iAssert ("x10" ↦ᵣ: fun _ => True)%I with "[H10]" as "H10Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld". iExists first, sp. iFrame "Hsys H10Any H2 HscratchFirst".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPostAt1566cEventsSpec).
  iExists sp, base, transactions, bytes, tail, first, second, items.
  iDestruct "Hpost" as "(HsysPost & H10Post & H2Post & HloadPost & _)".
  iFrame "HsysPost H10Post H2Post HloadPost H11 Hother Harray Hown
    HscratchLower HscratchBase HscratchLength HscratchPrefix HscratchSecond
    HscratchSuffix Hitems Hmmio Htrace HcallStack HP".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  all: try iExact "HP".
Qed.
