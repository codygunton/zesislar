Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import ZesuSsz.Automation.CallScratchBoolean.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientCopyToBoolean WriteSuccessExactTransactionsRecipientOutput
  WriteSuccessExactBooleanSpec.

Definition transactionRecipientOutputCallerFrame `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  ("x12" ↦ᵣ RVal_Bits (bv_sign_extend 64 last) ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗
   (bv_unsigned sp + 1648) ↦ₘ second ∗ (bv_unsigned sp + 1656) ↦ₘ last ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1764 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientOutputCallerFrame) := I.

Lemma transactions_recipient_boolean_to_output `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) tail (P : iProp Sigma) :
  encoderBooleanExactPost (BV 64 1) sp (BV 64 0x15180)
    (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
      (words_20_payload first second last) tail)
    (transactionRecipientCopiedFrame sp first second last P) -∗
  transactionRecipientOutputEntry sp (BV 64 0x15180) (BV 64 (mapIoContextAddress defaultMap))
    (sp - BV 64 9)%bv (BV 64 1) (words_20_payload first second last) tail
    (transactionRecipientOutputCallerFrame sp first second last P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & Hret & Hreturned & _)".
  iDestruct "Hreturned" as "(H5 & H10 & H11 & Hboolean & Hgap & Hmmio & Htrace & Hcaller & _)".
  iDestruct "Hcaller" as "(H12 & Hsrc0 & Hsrc1 & Hsrc2 & Hpayload & %Halign & %Hlow & %Hhigh & HP & _)".
  have HbooleanAddress : bv_unsigned (sp - BV 64 9)%bv = bv_unsigned sp - 9.
  { clear -Hlow. bv_solve. }
  iEval (rewrite /writeSuccessBooleanWordPayload mem_mapsto_array_singleton HbooleanAddress) in "Hboolean".
  iPoseProof (call_boolean_scratch_reuse sp (BV 64 0x15180) _
    with "[$Hgap $Hboolean $Hret]") as "Hscratch".
  have HpayloadAddress : bv_unsigned (sp + BV 64 1744)%bv = bv_unsigned sp + 1744.
  { clear -Hhigh. bv_solve. }
  iEval (rewrite -HpayloadAddress) in "Hpayload".
  unfold transactionRecipientOutputEntry, transactionRecipientOutputCallerFrame.
  iFrame. iPureIntro.
  rewrite /words_20_payload !length_app !length_bv_to_little_endian; done.
Qed.
Print Assumptions transactions_recipient_boolean_to_output.
