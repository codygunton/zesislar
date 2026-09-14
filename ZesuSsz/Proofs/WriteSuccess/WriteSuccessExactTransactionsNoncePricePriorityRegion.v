Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsNoncePricePriorityContinuation
  WriteSuccessExactTransactionsNonceToGasPrice WriteSuccessExactTransactionsNonceCall
  WriteSuccessExactTransactionsPriorityGasRegion WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsGasLimitCall WriteSuccessExactEncoderU128
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionNoncePricePriorityFrame `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) (P : iProp Sigma) : iProp Sigma :=
  transactionNonceGasPriceCaller sp gaslow gashigh
    ("x27" ↦ᵣ RVal_Bits tag ∗
     ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
      ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True) ∗ True).
Global Instance : LithiumUnfold (@transactionNoncePricePriorityFrame) := I.

Definition transactionNoncePricePriorityEntry `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh tag low high value oldra old5 old11 : bv 64)
    tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ reg_col [(KindReg "x10", BitsShape 64)] ∗
   (bv_unsigned sp + 272) ↦ₘ nonce ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned nonce)))
     (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
       (writeSuccessU128WordsPayload gaslow gashigh)
       (transactionPriorityGasTrace sp tag low high value tail))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 280 < 0x40000000⌝ ∗
   transactionNoncePricePriorityFrame sp gaslow gashigh tag low high value P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNoncePricePriorityEntry) := I.

Lemma transactions_nonce_price_priority_region_correct `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh tag low high value oldra old5 old11 : bv 64)
    tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high
      (transactionNonceGasPriceFrame sp nonce P))) -∗
  instr_body 0x150fc (transactionNoncePricePriorityEntry sp nonce gaslow gashigh
    tag low high value oldra old5 old11 tail P).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof (transactions_nonce_price_priority_continuation with "Hcode Hnext") as "#HnonceNext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (transactions_nonce_call_correct sp nonce oldra old5 old11
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload gaslow gashigh)
      (transactionPriorityGasTrace sp tag low high value tail))
    (transactionNoncePricePriorityFrame sp gaslow gashigh tag low high value P)
    with "[] Hint Houtput") as "Hcallee".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  iApply (instr_pre_wand 0x150fc 0x150fc false false with "Hcallee"); [done | done |].
  iIntros "Hentry".
  iEval (rewrite /transactionNoncePricePriorityEntry) in "Hentry".
  unfold transactionNonceEntry, transactionNoncePricePriorityFrame.
  iDestruct "Hentry" as "(Hsys & Hsp & H1 & H5 & H11 & Hregs & Hnonce & Hscratch & Hmmio & Htrace & Halign & Hlow & Hhigh & Hframe & _)".
  iFrame "HnonceNext". iFrame.
Qed.
Print Assumptions transactions_nonce_price_priority_region_correct.
