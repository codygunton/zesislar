From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1567c.

Definition writeSuccessTransactionsPostAt15684Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second data data9 : bv 64)
      (items : list ByteListItem) (saved : list valu)
      (r10 r11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674Caller) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost1567cSavedTail saved) ∗
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
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15684Spec) := I.

Lemma write_success_transactions_post_15680_move
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15684 (writeSuccessTransactionsPostAt15684Spec P) -∗
  instr_body 0x15680 (writeSuccessTransactionsPostAt15680Spec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup15680".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15680".
  iPoseProof ("Hlookup15680" $! 0x15680 with "[]") as "#Hinstr15680".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15680.
    done. }
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt15680Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transactions bytes tail first second data data9 items saved r10 r11)
    "(Hsys & Hcaller & Hsaved & HreturnOther & H2 & H8 & H9 & H10 & H11 &
      Hscratch & Hbase & Hown & Hitems & Hfacts & Hmmio & Htrace & HP & _)".
  iEval (unfold writeSuccessTransactionsPost1567cSavedTail) in "Hsaved".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hsaved".
  iDestruct "Hsaved" as
    "(H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  liARun.
  iEval (rewrite instr_pre'_eq) in "Hnext".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPostAt15684Spec).
  iExists sp, base, transactions, bytes, tail, first, second, data, data9,
    items, saved, r10, r11.
  iFrame "Hsys Hcaller HreturnOther H2 H8 H9 H11 Hscratch Hbase Hown Hitems
    Hfacts Hmmio Htrace HP".
  iFrame "Hsaved".
  iFrame.
Qed.
