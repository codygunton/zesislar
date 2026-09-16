Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientCopy WriteSuccessExactTransactionsRecipientBooleanCall
  WriteSuccessExactBooleanSpec.

Definition transactionRecipientCopiedFrame `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  ("x12" ↦ᵣ RVal_Bits (bv_sign_extend 64 last) ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗
   (bv_unsigned sp + 1648) ↦ₘ second ∗ (bv_unsigned sp + 1656) ↦ₘ last ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ words_20_payload first second last ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1764 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientCopiedFrame) := I.

Definition transactionRecipientCopyBooleanFrame `{!islaG Sigma} `{!threadG}
    (sp oldra old5 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 1)) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientCopyBooleanFrame) := I.

Lemma transactions_recipient_copy_to_boolean `{!islaG Sigma} `{!threadG}
    (sp first second oldra old5 : bv 64) (last : bv 32) tail (P : iProp Sigma) :
  transactionRecipientCopyPost sp first second last
    (transactionRecipientCopyBooleanFrame sp oldra old5 tail P) -∗
  instr_pre 0x15180 (encoderBooleanExactPost (BV 64 1) sp (BV 64 0x15180) tail
    (transactionRecipientCopiedFrame sp first second last P)) -∗
  transactionRecipientBooleanEntry true sp oldra first old5 second tail
    (transactionRecipientCopiedFrame sp first second last P).
Proof.
  iIntros "Hcopy Hnext".
  iDestruct "Hcopy" as "(Hsys & Hsp & H10 & H11 & H12 & Hsrc0 & Hsrc1 & Hsrc2 & Hdst0 & Hdst1 & Hdst2 & %Halign8 & %Hramlow & %Hhigh & Hframe & _)".
  iDestruct "Hframe" as "(H1 & H5 & Hscratch & Hmmio & Htrace & %Halign & %Hlow & HP & _)".
  iAssert ((bv_unsigned sp + 1744) ↦ₘ∗ words_20_payload first second last)%I
    with "[Hdst0 Hdst1 Hdst2]" as "Hpayload".
  { iApply words_20_payload_merge.
    replace (bv_unsigned sp + 1744 + 8)%Z with (bv_unsigned sp + 1752)%Z by lia.
    replace (bv_unsigned sp + 1744 + 16)%Z with (bv_unsigned sp + 1760)%Z by lia.
    iFrame. }
  unfold transactionRecipientBooleanEntry, encoderBooleanExactPrefixFrame,
    encoderBooleanExactFacts, transactionRecipientCopiedFrame.
  iFrame "Hsys H1 Hsp H10 Hscratch H5 H11 Hmmio Htrace Hnext H12 Hsrc0 Hsrc1 Hsrc2 Hpayload HP".
  repeat iSplit; iPureIntro; first [assumption | bv_solve].
Qed.
Print Assumptions transactions_recipient_copy_to_boolean.
