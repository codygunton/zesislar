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
Lemma transactions_source_signature_entry `{!islaG Sigma} `{!threadG}
 sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes tail (Q : iProp Sigma) :
 ⌜bv_unsigned sp `mod` 16 = 0⌝ -∗
 ⌜mapRamBase defaultMap <= bv_unsigned sp - 48⌝ -∗
 ⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ -∗
 transactionSourceAuthorizationExit sp base bytes processed index dataBytes accessBytes chainBytes
  entries blobBytes authBytes
  (transactionSourceSignatureEvents sp bytes index tail) Q -∗
 instr_pre 0x1565c (transactionSignatureSPost sp
  (transactionRowWord bytes index 128) (transactionRowWord bytes index 136)
  (transactionRowWord bytes index 144) (transactionRowWord bytes index 152) tail
  (transactionSignatureRFrame sp (transactionRowWord bytes index 96) (transactionRowWord bytes index 104)
   (transactionRowWord bytes index 112) (transactionRowWord bytes index 120)
   (transactionSignatureVFrame sp (transactionRowWord bytes index 256) (transactionSourceSignatureLoan sp base bytes processed index dataBytes accessBytes chainBytes
    entries blobBytes (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I ∗
   transactionSourceSignatureCommonFrame sp bytes index)))) -∗
 (∃ oldra old5 old11 : bv 64,
 transactionSignatureVRSEntry sp (transactionRowWord bytes index 256)
  (transactionRowWord bytes index 96) (transactionRowWord bytes index 104)
  (transactionRowWord bytes index 112) (transactionRowWord bytes index 120)
  (transactionRowWord bytes index 128) (transactionRowWord bytes index 136)
  (transactionRowWord bytes index 144) (transactionRowWord bytes index 152)
  oldra old5 old11 tail
  (transactionSourceSignatureLoan sp base bytes processed index dataBytes accessBytes chainBytes
    entries blobBytes (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I ∗
   transactionSourceSignatureCommonFrame sp bytes index))%I.
Proof.
 iIntros (Halign Hlow Hhigh) "Hexit Hnext".
 unfold transactionSourceAuthorizationExit.
 iDestruct "Hexit" as "(Hsys & Hsp & Hregs & H18 & Hupper & Hmmio & Htrace & H144 & H152 & H160 & Hframe & _)".
 iPoseProof (transactions_source_signature_memory with "Hframe") as "(Hpair & Hwords & Hlower & Hloan)".
 iEval (unfold transactionSourceSignatureWords) in "Hwords".
 iDestruct "Hwords" as "(Hv & Hr3 & Hr2 & Hr1 & Hs0 & Hr0 & Hs3 & Hs2 & Hs1 & _)".
 iEval (rewrite !reg_col_cons reg_col_nil) in "Hregs".
 zesu_open_resource_groups; zesu_open_bits_registers.
 iExists _, _, _.
 unfold transactionSignatureVRSEntry, transactionSignatureVCaller,
  transactionSignatureRFrame, transactionSignatureSFrame, transactionSourceSignatureCommonFrame.
 iEval (unfold transactionSourceSignatureEvents) in "Htrace".
 iFrame "Hsys Hsp Hloan H18 H144 H152 H160 Hmmio Htrace Hnext".
 zesu_run.
 iPureIntro; bv_solve.
Qed.
Print Assumptions transactions_source_signature_entry.
