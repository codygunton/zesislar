Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientBooleanToOutput WriteSuccessExactTransactionsRecipientOutput
  WriteSuccessExactTransactionsValueCall WriteSuccessExactEncoderU256Spec.

Definition transactionRecipientValuePreparation `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 old13 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x13" ↦ᵣ RVal_Bits old13 ∗ "x18" ↦ᵣ RVal_Bits w0 ∗
   "x20" ↦ᵣ RVal_Bits w1 ∗ (bv_unsigned sp + 128) ↦ₘ w2 ∗
   "x21" ↦ᵣ RVal_Bits w3 ∗ (bv_unsigned sp - 48) ↦ₘ? 32 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientValuePreparation) := I.

Definition transactionRecipientValueSourceFrame `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1640) ↦ₘ first ∗
   (bv_unsigned sp + 1648) ↦ₘ second ∗ (bv_unsigned sp + 1656) ↦ₘ last ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ words_20_payload first second last ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientValueSourceFrame) := I.

Lemma transactions_recipient_output_to_value `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 old13 : bv 64) (last : bv 32)
    tail (P : iProp Sigma) :
  transactionRecipientOutputPost sp (words_20_payload first second last)
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail)
    (transactionRecipientOutputCallerFrame sp first second last
      (transactionRecipientValuePreparation sp w0 w1 w2 w3 old13 P)) -∗
  instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientValueSourceFrame sp first second last P)) -∗
  transactionValueEntry sp w0 w1 w2 w3 (BV 64 0x15190) (BV 64 (mapIoContextAddress defaultMap)) tail
    (transactionRecipientValueSourceFrame sp first second last P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & H5 & H10 & H11 & Hpayload & Hmmio & Htrace & HspCaller & _)".
  iDestruct "HspCaller" as "(Hsp & Hcaller & _)".
  iDestruct "Hcaller" as "(H12 & Hsrc0 & Hsrc1 & Hsrc2 & Hupper & %Halign16 & %Hlow16 & %Hhigh16 & Hprepare & _)".
  iDestruct "Hprepare" as "(H13 & H18 & H20 & Hword2 & H21 & Hlower & %Halign & %Hlow & %Hhigh & HP & _)".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I with "[Hlower Hupper]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
    replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia.
    iExact "Hupper". }
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])%I
    with "[H10 H11 H12 H13]" as "Hregs".
  { iApply (reg_col_bv_list_shape [("x10", (sp + BV 64 1744)%bv); ("x11", BV 64 20);
      ("x12", bv_sign_extend 64 last); ("x13", old13)]).
    cbn. iFrame. }
  unfold transactionValueEntry, transactionValueFrame, transactionRecipientValueSourceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_output_to_value.
