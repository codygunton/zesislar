Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitWords.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessExactTransactionsSourceSignatureLoanSpec
 WriteSuccessExactTransactionsSourceSignatureMemoryLoan
 WriteSuccessExactTransactionsSourceAuthorizationSpec
 WriteSuccessExactTransactionsSignatureVRS
 WriteSuccessExactTransactionsSignatureVToR
 WriteSuccessExactTransactionsSignatureVCall
 WriteSuccessExactTransactionsSignatureRCall
 WriteSuccessExactTransactionsSignatureSCall
 WriteSuccessExactTransactionsGasLoads
 WriteSuccessExactTransactionsSourceFieldLayout
 WriteSuccessObservation WriteSuccessOutputSemantic WriteSuccessStorageKeysSpec
 WriteSuccessTransactionsSpec
 WriteSuccessExactTransactionsSourceSuffixModel.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeCode WriteSuccessExactTransactionsSignatureCompleteCode WriteSuccessExactTransactionsSourceSignatureEntry WriteSuccessExactTransactionsSourceSignatureExit.
Lemma transactions_source_signature_continuation `{!islaG Sigma} `{!threadG}
 sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes tail (Q : iProp Sigma) :
 bv_unsigned sp `mod` 16 = 0 ->
 mapRamBase defaultMap <= bv_unsigned sp - 48 ->
 bv_unsigned sp + 1896 < machineRamEnd defaultMap ->
 writeSuccessCompleteNativeCode -∗
 □ instr_pre 0x1565c (transactionSourceAuthorizationExit sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes tail Q) -∗
 □ instr_pre 0x15620 (transactionSourceAuthorizationExit sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes
  (transactionSourceSignatureEvents sp bytes index tail) Q).
Proof.
 intros Halign Hlow Hhigh. iIntros "#Hcode #Hexit".
 iAssert (□ instr_pre 0x1565c (transactionSignatureSPost sp (transactionRowWord bytes index 128) (transactionRowWord bytes index 136) (transactionRowWord bytes index 144) (transactionRowWord bytes index 152) tail (transactionSignatureRFrame sp (transactionRowWord bytes index 96) (transactionRowWord bytes index 104) (transactionRowWord bytes index 112) (transactionRowWord bytes index 120) (transactionSignatureVFrame sp (transactionRowWord bytes index 256) (transactionSourceSignatureLoan sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I ∗ transactionSourceSignatureCommonFrame sp bytes index)%I))))%I as "#Hreturned".
 { iModIntro. iEval (rewrite instr_pre'_eq) in "Hexit".
   iEval (rewrite instr_pre'_eq). iNext. iIntros "Hpost".
   iPoseProof (transactions_source_signature_exit with "Hpost") as "Hsource".
   iApply ("Hexit" with "Hsource"). }
 iModIntro. iEval (rewrite instr_pre'_eq). iNext. iIntros "Hsource".
 iPoseProof (transactions_source_signature_entry with "[] [] [] Hsource Hreturned")
  as (oldra old5 old11) "Hentry"; [done | done | done |].
 iPoseProof (transactions_signature_complete_code sp (transactionRowWord bytes index 256)
  (transactionRowWord bytes index 96) (transactionRowWord bytes index 104) (transactionRowWord bytes index 112) (transactionRowWord bytes index 120) (transactionRowWord bytes index 128) (transactionRowWord bytes index 136) (transactionRowWord bytes index 144) (transactionRowWord bytes index 152)
  oldra old5 old11 tail (transactionSourceSignatureLoan sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I ∗ transactionSourceSignatureCommonFrame sp bytes index)%I with "Hcode") as "Hbody".
 iEval (rewrite instr_pre'_eq) in "Hbody".
 iApply ("Hbody" with "Hentry").
Qed.
Print Assumptions transactions_source_signature_continuation.
