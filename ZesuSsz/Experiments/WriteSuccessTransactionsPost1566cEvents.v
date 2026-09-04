From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668Events.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import IslaTraces.write_success_87.a1566c_spec.

Definition writeSuccessTransactionsPostAt15670EventsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second ra : bv 64)
      (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ra ∗
    reg_col writeSuccessTransactionsPostOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗ base ↦ₘ∗ bytes ∗
    writeSuccessTransactionsOwn transactions ∗
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
    (@writeSuccessTransactionsPostAt15670EventsSpec) := I.

Lemma write_success_transactions_post_1566c_events
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15670 (writeSuccessTransactionsPostAt15670EventsSpec P) -∗
  instr_body 0x1566c (writeSuccessTransactionsPostAt1566cEventsSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup1566c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1566c".
  iPoseProof ("Hlookup1566c" $! 0x1566c with "[]") as "#Hinstr1566c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1566c. done. }
  iPoseProof (IslaTraces.write_success_87.a1566c_spec.a1566c_spec
    0x1566c with "Hinstr1566c") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt1566cEventsSpec) in "Hentry".
  iDestruct "Hentry" as (sp base transactions bytes tail first second items)
    "(Hsys & Hother & H2 & H10 & H11 & Harray & Hown & HscratchLower &
      HscratchBase & HscratchLength & HscratchPrefix & HscratchFirst & HscratchSecond &
      HscratchSuffix & Hitems & %Hfacts & Hmmio & Htrace & (Hq & _))".
  iDestruct "Hq" as "(HcallStack & %HspAlign16 & %HspAlign8 &
    %HspLower & %HspUpper & HP)".
  iDestruct (reg_col_lookup writeSuccessTransactionsOtherRegShapes 0%nat
    (KindReg "x1", BitsShape 64) with "Hother") as (ra Hra) "(Hx1 & Hother)".
  { vm_compute. reflexivity. }
  apply valu_has_bits_shape in Hra as (raBits & ->).
  destruct Hfacts as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
  iAssert ("x11" ↦ᵣ: fun _ => True)%I with "[H11]" as "H11Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld". iExists second, sp. iFrame "Hsys H11Any H2 HscratchSecond".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPostAt15670EventsSpec).
  iExists sp, base, transactions, bytes, tail, first, second, raBits, items.
  iDestruct "Hpost" as "(HsysPost & H11Post & H2Post & HloadPost & _)".
  iFrame "HsysPost H10 H11Post H2Post HloadPost Hx1 Hother Harray Hown
    HscratchLower HscratchBase HscratchLength HscratchPrefix HscratchFirst
    HscratchSuffix Hitems Hmmio Htrace HcallStack HP".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  all: try iExact "HP".
Qed.
