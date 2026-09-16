Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1567c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15680.
Require Import IslaTraces.write_success_88.a15684_spec.
Require Import InstrSpecs.Specs.

Definition writeSuccessTransactionsPost15684Caller : list string :=
  ["x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x5"; "x6"; "x7"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactionsPostAt15688Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second data data9 : bv 64)
      (items : list ByteListItem) (saved : list valu)
      (r11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15684) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15684Caller) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost1567cSavedTail saved) ∗
    ⌜length saved = 10%nat⌝ ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits data ∗
    "x9" ↦ᵣ RVal_Bits data9 ∗
    "x10" ↦ᵣ RVal_Bits data9 ∗
    "x11" ↦ᵣ RVal_Bits r11 ∗
    writeSuccessTransactionsPost15680Scratch sp base (length transactions)
      first second ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15688Spec) := I.

Lemma write_success_transactions_post_15684_auipc
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15688 (writeSuccessTransactionsPostAt15688Spec P) -∗
  instr_body 0x15684 (writeSuccessTransactionsPostAt15684Spec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup15684".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15684".
  iPoseProof ("Hlookup15684" $! 0x15684 with "[]") as "#Hinstr15684".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15684.
    done. }
  iPoseProof (IslaTraces.write_success_88.a15684_spec.a15684_spec
    0x15684 with "Hinstr15684") as "Hauipc".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt15684Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transactions bytes tail first second data data9 items saved r10 r11)
    "(Hsys & Hcaller & Hsaved & %HsavedLength & HreturnOther & H2 & H8 & H9 & H10 & H11 &
      Hscratch & Hbase & Hown & Hitems & Hfacts & HspUpper & Hmmio & Htrace & HP & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hcaller".
  iDestruct "Hcaller" as
    "(H1Old & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "H1Old" as (v1old) "(%Hv1old & H1Old)".
  iAssert ("x1" ↦ᵣ: (fun _ => True))%I with "[H1Old]" as "H1Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v1old. iFrame. }
  iEval (rewrite /a15684_auipc_spec).
  iApply "Hauipc".
  iFrame "Hsys H1Any".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & H1Post & _)".
  have Hx1 : Z_to_bv 64 87684 = BV 64 0x15684 by bv_solve.
  iEval (rewrite Hx1) in "H1Post".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPostAt15688Spec).
  iExists sp, base, transactions, bytes, tail, first, second, data, data9,
    items, saved, r11.
  iFrame "HsysPost H1Post H12 H13 H14 H15 H16 H17 H5 H6 H7 H28 H29 H30 H31
    Hsaved HreturnOther H2 H8 H9 H10 H11 Hscratch Hbase Hown Hitems Hfacts
    HspUpper Hmmio Htrace HP".
  iEval (simpl).
  iPureIntro; split; [done|exact HsavedLength].
Qed.
