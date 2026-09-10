Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1567c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15684.
Require Import IslaTraces.write_success_88.a15688_spec.

Definition writeSuccessTransactionsPostAt15d10Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second data data9 : bv 64)
      (items : list ByteListItem) (saved : list valu)
      (r11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 0x1568c) ∗
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
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15d10Spec) := I.

Lemma write_success_transactions_post_15688_jump
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15d10 (writeSuccessTransactionsPostAt15d10Spec P) -∗
  instr_body 0x15688 (writeSuccessTransactionsPostAt15688Spec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup15688".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15688".
  iPoseProof ("Hlookup15688" $! 0x15688 with "[]") as "#Hinstr15688".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15688.
    done. }
  iPoseProof (IslaTraces.write_success_88.a15688_spec.a15688_spec
    0x15688 with "Hinstr15688") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt15688Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transactions bytes tail first second data data9 items saved r11)
    "(Hsys & H1 & Hcaller & Hsaved & %HsavedLength & HreturnOther & H2 & H8 &
      H9 & H10 & H11 & Hscratch & Hbase & Hown & Hitems & Hfacts & HspUpper &
      Hmmio & Htrace & HP & _)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15684).
  iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15684) + BV 64 1676)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15d10
    by bv_solve.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand with "Hnext").
  { done. }
  { bv_solve. }
  iIntros "Hbasic".
  iDestruct "Hbasic" as "(Hsys & H1 & _)".
  iEval (rewrite /writeSuccessTransactionsPostAt15d10Spec).
  iExists sp, base, transactions, bytes, tail, first, second, data, data9,
    items, saved, r11.
  iFrame "Hsys H1 Hcaller Hsaved HreturnOther H2 H8 H9 H10 H11 Hscratch Hbase
    Hown Hitems Hfacts HspUpper Hmmio Htrace HP".
  iPureIntro. exact HsavedLength.
Qed.
