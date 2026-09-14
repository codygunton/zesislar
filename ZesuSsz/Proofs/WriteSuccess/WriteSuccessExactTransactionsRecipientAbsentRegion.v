Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientAbsentToValue
  WriteSuccessExactTransactionsRecipientAbsentValueContinuation WriteSuccessExactTransactionsRecipientBooleanCall
  WriteSuccessExactTransactionsValueCall WriteSuccessExactEncoderU256Spec
  WriteSuccessExactBooleanSpec.

Definition transactionRecipientAbsentEntry `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 oldra old5 old11 old12 old13 : bv 64)
    (last : bv 32) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x10" ↦ᵣ RVal_Bits (BV 64 0) ∗ "x11" ↦ᵣ RVal_Bits old11 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 0))
     (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
       (writeSuccessU256WordsPayload w0 w1 w2 w3) tail)) ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < 0x40000000⌝ ∗
   transactionRecipientAbsentValuePreparation sp first second w0 w1 w2 w3 old12 old13 last P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientAbsentEntry) := I.

Lemma transactions_recipient_absent_region_correct `{!islaG Sigma} `{!threadG}
    (sp first second w0 w1 w2 w3 oldra old5 old11 old12 old13 : bv 64)
    (last : bv 32) tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientAbsentValueSourceFrame sp first second last P)) -∗
  instr_body 0x15194 (transactionRecipientAbsentEntry sp first second w0 w1 w2 w3
    oldra old5 old11 old12 old13 last tail P).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (transactions_recipient_absent_value_continuation with "Hcode Hnext") as "#HbooleanNext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (transactions_recipient_boolean_call_correct false sp oldra (BV 64 0) old5 old11
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail)
    (transactionRecipientAbsentValuePreparation sp first second w0 w1 w2 w3 old12 old13 last P)
    with "[] Hboolean Houtput") as "Hcallee".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iApply (instr_pre_wand 0x15194 0x15194 false false with "Hcallee"); [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as "(Hsys & Hsp & H1 & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & %Halign4 & %Halign3 & %Hlow & %Hhigh & Hprepare & _)".
  unfold transactionRecipientBooleanEntry, encoderBooleanExactPrefixFrame, encoderBooleanExactFacts.
  iFrame "HbooleanNext". iFrame. repeat iSplit; try done; iPureIntro; bv_solve.
Qed.
Print Assumptions transactions_recipient_absent_region_correct.
