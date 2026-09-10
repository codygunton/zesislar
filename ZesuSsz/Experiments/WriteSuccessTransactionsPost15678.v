From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.

Definition writeSuccessTransactionsPost15674SavedTail : list string :=
  ["x9"; "x18"; "x19"; "x20"; "x21";
   "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessTransactionsPost1567cScratch
    `{!islaG Sigma} (sp : bv 64) (base : Z) (total : nat)
    (first second : bv 64) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 984 ∗
   (bv_unsigned sp + 1104) ↦ₘ first ∗
   (bv_unsigned sp + 1112) ↦ₘ second ∗
   (bv_unsigned sp + 1128) ↦ₘ? 768 ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost1567cScratch) := I.

Definition writeSuccessTransactionsPostAt1567cSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second data : bv 64)
      (items : list ByteListItem) (saved : list valu)
      (r10 r11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674Caller) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost15674SavedTail saved) ∗
    ⌜length saved = 11%nat⌝ ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits data ∗
    "x10" ↦ᵣ RVal_Bits r10 ∗
    "x11" ↦ᵣ RVal_Bits r11 ∗
    writeSuccessTransactionsPost1567cScratch sp base (length transactions)
      first second ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt1567cSpec) := I.

Lemma write_success_transactions_post_15678_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x1567c (writeSuccessTransactionsPostAt1567cSpec P) -∗
  instr_body 0x15678 (writeSuccessTransactionsPost15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup15678".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15678".
  iPoseProof ("Hlookup15678" $! 0x15678 with "[]") as "#Hinstr15678".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15678.
    done. }
  iPoseProof (IslaTraces.write_success_88.a15678_spec.a15678_spec
    0x15678 with "Hinstr15678") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost15678Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transactions bytes tail first second items saved r10 r11)
    "(Hsys & Hcaller & Hsaved & %HsavedLength & HreturnOther & H2 & H10 & H11 & Hscratch &
      Hbase & Hown & Hitems & Hfacts & HspUpper & Hmmio & Htrace & HP & _)".
  destruct saved as [|v8 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v9 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v18 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v19 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v20 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v21 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v22 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v23 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v24 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v25 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v26 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v27 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|vrest rest]; cbn in HsavedLength; try lia.
  iEval (unfold writeSuccessTransactionsPost15674SavedTail) in "Hsaved".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iEval (unfold writeSuccessTransactionsPostScratch15670) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & HbaseWord & HlengthWord & HscratchPrefix & HscratchFirst &
      HscratchSecond & HscratchSuffix & _)".
  iDestruct (mem_mapsto_uninit_split 8 with "HscratchSuffix") as
    "(Hload & Hsuffix)"; first lia.
  have HloadAddress : bv_unsigned sp + 1120 + 8 = bv_unsigned sp + 1128 by lia.
  iEval (rewrite HloadAddress; replace (776 - 8)%Z with 768%Z by lia)
    in "Hsuffix".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hload") as
    (n data HdataLength) "Hload".
  cbn in HdataLength. subst n.
  iDestruct "H8" as (v8old) "(%Hv8old & H8)".
  iAssert ("x8" ↦ᵣ: (fun _ => True))%I with "[H8]" as "H8Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. }
  iDestruct "Hfacts" as %Hfacts.
  iDestruct "HspUpper" as %HspUpper.
  have HspLower : (0x20000000 <= bv_unsigned sp - 80)%Z.
  { destruct Hfacts as
      (HsecondLength & HitemsLength & HfirstAlign & HfirstLower &
       HfirstUpper & HspExtract & HspLower' & HspMax).
    exact HspLower'. }
  have HspAlign8 : (bv_unsigned sp `mod` 8 = 0)%Z.
  { destruct Hfacts as
      (HsecondLength & HitemsLength & HfirstAlign & HfirstLower &
       HfirstUpper & HspExtract & HspLowerFact & HspMax).
    have HspExtractU := f_equal bv_unsigned HspExtract.
    rewrite bv_extract_0_unsigned in HspExtractU.
    cbn in HspExtractU.
    bv_solve. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld".
  iExists data, sp.
  iFrame "Hsys H8Any H2 Hload".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia; try iFrame.
  all: try (iPureIntro; lia).
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & H8Post & H2Post & HloadPost & _)".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPostAt1567cSpec).
  iExists sp, base, transactions, bytes, tail, first, second, data, items,
    [v9; v18; v19; v20; v21; v22; v23; v24; v25; v26; v27], r10, r11.
  iFrame "HsysPost Hcaller HreturnOther".
  iEval (unfold writeSuccessTransactionsPost15674SavedTail).
  iEval (rewrite !reg_col_cons reg_col_nil).
  iFrame "H2Post H8Post H10 H11 Hsuffix HbaseWord HlengthWord HscratchPrefix
    HscratchFirst HscratchSecond Hbase Hown Hitems Hlower H9 H18 H19 H20 H21 H22
    H23 H24 H25 H26 H27".
  iSplit; first (iPureIntro; reflexivity).
  iSplit; first (iPureIntro; exact Hfacts).
  iSplit; first (iPureIntro; exact HspUpper).
  iFrame "Hmmio Htrace HP".
Qed.
