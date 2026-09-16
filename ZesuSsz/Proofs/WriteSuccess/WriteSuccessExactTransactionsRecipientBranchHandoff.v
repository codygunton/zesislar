Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientBranch WriteSuccessExactTransactionsRecipientCopy
  WriteSuccessExactTransactionsRecipientCopyToBoolean WriteSuccessExactTransactionsRecipientOutputToValue
  WriteSuccessExactTransactionsRecipientAbsentRegion WriteSuccessExactTransactionsRecipientAbsentToValue
  WriteSuccessExactEncoderU256Spec WriteSuccessExactBooleanSpec.

Definition transactionRecipientValueTrace
    (sp tag first second w0 w1 w2 w3 : bv 64) (last : bv 32) tail : spec :=
  let value := writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
    (writeSuccessU256WordsPayload w0 w1 w2 w3) tail in
  if bool_decide (tag = BV 64 0)
  then writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
    (writeSuccessBooleanWordPayload (BV 64 0)) value
  else writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
    (writeSuccessBooleanWordPayload (BV 64 1))
    (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
      (words_20_payload first second last) value).

Definition transactionRecipientBranchCallerFrame `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 oldra old5 old11 old12 old13 : bv 64)
    (last : bv 32) tail (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ "x12" ↦ᵣ RVal_Bits old12 ∗
   "x13" ↦ᵣ RVal_Bits old13 ∗ "x18" ↦ᵣ RVal_Bits w0 ∗
   "x20" ↦ᵣ RVal_Bits w1 ∗ (bv_unsigned sp + 128) ↦ₘ w2 ∗
   "x21" ↦ᵣ RVal_Bits w3 ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗ (bv_unsigned sp + 1648) ↦ₘ second ∗
   (bv_unsigned sp + 1656) ↦ₘ last ∗ (bv_unsigned sp + 1744) ↦ₘ? 20 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (transactionRecipientValueTrace sp tag first second w0 w1 w2 w3 last tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientBranchCallerFrame) := I.

Lemma transactions_recipient_branch_to_present `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 oldra old5 old11 old12 old13 : bv 64)
    (last : bv 32) tail (P : iProp Sigma) :
  (transactionRecipientBranchState sp tag tag
    (transactionRecipientBranchCallerFrame sp tag first second w0 w1 w2 w3
      oldra old5 old11 old12 old13 last tail P) ∗ ⌜tag <> BV 64 0⌝ ∗ True)%I -∗
  transactionRecipientCopyEntry sp first second last
    (transactionRecipientCopyBooleanFrame sp oldra old5
      (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
        (words_20_payload first second last)
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
          (writeSuccessU256WordsPayload w0 w1 w2 w3) tail))
      (transactionRecipientValuePreparation sp w0 w1 w2 w3 old13
        ((bv_unsigned sp + 120) ↦ₘ tag ∗ P ∗ True))).
Proof.
  iIntros "(Hstate & %Htag & _)".
  iDestruct "Hstate" as "(Hsys & Hsp & H10 & HtagMemory & %Halign8 & %Hlow8 & %Hhigh8 & Hcaller & _)".
  iDestruct "Hcaller" as "(H1 & H5 & H11 & H12 & H13 & H18 & H20 & Hword2 & H21 & Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Hscratch & Hmmio & Htrace & %Halign & %Hlow & %Hhigh & HP & _)".
  iEval (rewrite /transactionRecipientValueTrace bool_decide_false //) in "Htrace".
  iDestruct (mem_mapsto_uninit_split 32 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64)])%I with "[H10 H11 H12]" as "Hregs".
  { iApply (reg_col_bv_list_shape [("x10", tag); ("x11", old11); ("x12", old12)]).
    cbn. iFrame. }
  unfold transactionRecipientCopyEntry, transactionRecipientCopyBooleanFrame,
    transactionRecipientValuePreparation.
  iFrame. repeat iSplit; try done; iPureIntro; first [lia | bv_solve].
Qed.
Print Assumptions transactions_recipient_branch_to_present.
