Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15668.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668.

Definition writeSuccessTransactionsPostScratch15670
    `{!islaG Sigma} (sp : bv 64) (base : Z) (total : nat)
    (first second : bv 64) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 984 ∗
   (bv_unsigned sp + 1104) ↦ₘ first ∗
   (bv_unsigned sp + 1112) ↦ₘ second ∗
   (bv_unsigned sp + 1120) ↦ₘ? 776 ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostScratch15670) := I.

Definition writeSuccessTransactionsPostOtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18"; "x19";
   "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactionsPostOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactionsPostOtherRegisters.

Definition writeSuccessTransactionsPostAt15670Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second ra : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ra ∗
    reg_col writeSuccessTransactionsPostOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗
    base ↦ₘ∗ bytes ∗
    writeSuccessTransactionsOwn transactions ∗
    (writeSuccessTransactionsPostScratch15670 sp base (length transactions)
      first second) ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
    ((bv_unsigned sp) ↦ₘ? 104 ∗
     (bv_unsigned sp + 1896) ↦ₘ? 104 ∗
     ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
     ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
     ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
     ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15670Spec) := I.

Lemma write_success_transactions_post_1566c_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15670 (writeSuccessTransactionsPostAt15670Spec P) -∗
  instr_body 0x1566c (writeSuccessTransactionsPostAt1566cSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup1566c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1566c".
  iPoseProof ("Hlookup1566c" $! 0x1566c with "[]") as "#Hinstr1566c".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a1566c.
    done. }
  iPoseProof (IslaTraces.write_success_87.a1566c_spec.a1566c_spec
    0x1566c with "Hinstr1566c") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt1566cSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transactions bytes tail first)
    "(Hsys & Hother & H2 & H10 & H11 & Harray & Hown & Hscratch &
      Hmmio & Htrace & Hq & _)".
  iDestruct (reg_col_lookup writeSuccessTransactionsOtherRegShapes 0%nat
    (KindReg "x1", BitsShape 64) with "Hother") as
    (ra Hra) "(Hx1 & Hother)".
  { vm_compute. reflexivity. }
  apply valu_has_bits_shape in Hra as (raBits & ->).
  iDestruct "Hq" as
    "(HlowerFrame & HsavedFrame & %HspAlign16 & %HspAlign8 &
      %HspLower & %HspUpper & HP)".
  iEval (rewrite /writeSuccessTransactionsPostScratch1566c) in "Hscratch".
  iDestruct "Hscratch" as
    "(HscratchLower & HscratchBase & HscratchLength & HscratchPrefix &
      HscratchFirst & HscratchRest & _)".
  iDestruct (mem_mapsto_uninit_split 8 with "HscratchRest") as
    "(HscratchSecond & HscratchSuffix)"; first lia.
  have HscratchSecondAddress :
      bv_unsigned sp + 1112 + 8 = bv_unsigned sp + 1120 by lia.
  iEval (rewrite HscratchSecondAddress;
    replace (784 - 8)%Z with 776%Z by lia) in "HscratchSuffix".
  iDestruct (mem_mapsto_uninit_to_mapsto with "HscratchSecond") as
    (n second HsecondLength) "HscratchSecond".
  cbn in HsecondLength. subst n.
  iAssert ("x11" ↦ᵣ: fun _ => True)%I with "[H11]" as "H11Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld".
  iExists second, sp.
  iFrame "Hsys H11Any H2 HscratchSecond".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPostAt15670Spec).
  iExists sp, base, transactions, bytes, tail, first, second, raBits.
  iDestruct "Hpost" as
    "(HsysPost & H11Post & H2Post & HloadPost & _)".
  iFrame "HsysPost H10 H11Post H2Post HloadPost Hx1 Hother Harray Hown
    HscratchLower HscratchBase HscratchLength HscratchPrefix HscratchFirst
    HscratchSuffix Hmmio Htrace HlowerFrame HsavedFrame HP".
  repeat iSplit; try iPureIntro; try assumption; try lia.
Qed.
