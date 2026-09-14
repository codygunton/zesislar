Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.CallScratchBoolean.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsValueCall WriteSuccessExactEncoderU256Spec
  WriteSuccessExactBooleanSpec.

Definition transactionRecipientAbsentValuePreparation `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 old12 old13 : bv 64)
    (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  ("x12" ↦ᵣ RVal_Bits old12 ∗ "x13" ↦ᵣ RVal_Bits old13 ∗
   "x18" ↦ᵣ RVal_Bits w0 ∗ "x20" ↦ᵣ RVal_Bits w1 ∗
   (bv_unsigned sp + 128) ↦ₘ w2 ∗ "x21" ↦ᵣ RVal_Bits w3 ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗ (bv_unsigned sp + 1648) ↦ₘ second ∗
   (bv_unsigned sp + 1656) ↦ₘ last ∗ (bv_unsigned sp + 1744) ↦ₘ? 20 ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAbsentValuePreparation) := I.

Definition transactionRecipientAbsentValueSourceFrame `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1640) ↦ₘ first ∗ (bv_unsigned sp + 1648) ↦ₘ second ∗
   (bv_unsigned sp + 1656) ↦ₘ last ∗ (bv_unsigned sp + 1744) ↦ₘ? 20 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAbsentValueSourceFrame) := I.

Lemma transactions_recipient_absent_boolean_to_value `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 old12 old13 : bv 64) (last : bv 32)
    tail (P : iProp Sigma) :
  encoderBooleanExactPost (BV 64 0) sp (BV 64 0x1519c)
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail)
    (transactionRecipientAbsentValuePreparation sp first second w0 w1 w2 w3 old12 old13 last P) -∗
  instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientAbsentValueSourceFrame sp first second last P)) -∗
  transactionValueEntry sp w0 w1 w2 w3 (BV 64 0x1519c) (BV 64 0x2401a0b8) tail
    (transactionRecipientAbsentValueSourceFrame sp first second last P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & Hret & Hreturned & _)".
  iDestruct "Hreturned" as "(H5 & H10 & H11 & Hboolean & Hgap & Hmmio & Htrace & Hprepare & _)".
  iDestruct "Hprepare" as "(H12 & H13 & H18 & H20 & Hword2 & H21 & Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Hlower & %Halign & %Hlow & %Hhigh & HP & _)".
  have Haddress : bv_unsigned (sp - BV 64 9)%bv = bv_unsigned sp - 9.
  { clear -Hlow. bv_solve. }
  iEval (rewrite /writeSuccessBooleanWordPayload mem_mapsto_array_singleton Haddress) in "Hboolean".
  iPoseProof (call_boolean_scratch_reuse sp (BV 64 0x1519c) _
    with "[$Hgap $Hboolean $Hret]") as "Hupper".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I with "[Hlower Hupper]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
    replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia.
    iExact "Hupper". }
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])%I
    with "[H10 H11 H12 H13]" as "Hregs".
  { iApply (reg_col_bv_list_shape [("x10", (sp - BV 64 9)%bv); ("x11", BV 64 1);
      ("x12", old12); ("x13", old13)]).
    cbn. iFrame. }
  unfold transactionValueEntry, transactionValueFrame, transactionRecipientAbsentValueSourceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_absent_boolean_to_value.
