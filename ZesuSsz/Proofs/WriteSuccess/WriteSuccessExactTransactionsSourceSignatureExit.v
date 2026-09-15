Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitWords.
Require Import ZesuSsz.Automation.CallScratch.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessTransactionsSpec WriteSuccessExactEncoderU256Spec
 WriteSuccessExactTransactionsGasLoads
 WriteSuccessExactTransactionsSourceSignatureLoanSpec
 WriteSuccessExactTransactionsSourceAuthorizationSpec
 WriteSuccessExactTransactionsSignatureVCall
 WriteSuccessExactTransactionsSignatureRCall
 WriteSuccessExactTransactionsSignatureSCall.
Lemma transactions_source_signature_exit `{!islaG Sigma} `{!threadG}
 sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes authBytes tail (Q : iProp Sigma) :
 transactionSignatureSPost sp
  (transactionRowWord bytes index 128) (transactionRowWord bytes index 136)
  (transactionRowWord bytes index 144) (transactionRowWord bytes index 152) tail
  (transactionSignatureRFrame sp (transactionRowWord bytes index 96) (transactionRowWord bytes index 104)
   (transactionRowWord bytes index 112) (transactionRowWord bytes index 120)
   (transactionSignatureVFrame sp (transactionRowWord bytes index 256) (transactionSourceSignatureLoan sp base bytes processed index dataBytes accessBytes chainBytes
 entries blobBytes (writeSuccessByteArrayOwn (transactionRowWord bytes index 240) authBytes ∗ Q)%I ∗
 transactionSourceSignatureCommonFrame sp bytes index)%I)) -∗
 transactionSourceAuthorizationExit sp base bytes processed index dataBytes accessBytes chainBytes
  entries blobBytes authBytes tail Q.
Proof.
 iIntros "Hpost".
 iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hsframe & _)".
 iDestruct "Hsframe" as "(Hs0 & Hs1 & Hs2 & Hs3 & %Halign & %Hlow & %Hhigh & Hrframe & _)".
 iDestruct "Hrframe" as "(Hr0 & Hr1 & Hr2 & Hr3 & _ & _ & _ & Hvframe & _)".
 iDestruct "Hvframe" as "(Hv & _ & _ & _ & Hcaller & _)".
 iDestruct "Hcaller" as "[Hloan Hcommon]".
 have Hlen : length (writeSuccessU256WordsPayload (transactionRowWord bytes index 128)
  (transactionRowWord bytes index 136) (transactionRowWord bytes index 144)
  (transactionRowWord bytes index 152)) = 32%nat by reflexivity.
 iPoseProof (call_scratch_reuse sp (BV 64 0x1565c) _ Hlen Hlow
  with "[$Hpayload $Hgap $Hret]") as "Hscratch".
 iAssert ((reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
  transactionSourceSignatureWords sp bytes index ∗ (bv_unsigned sp - 48) ↦ₘ? 16 ∗
  (bv_unsigned sp - 32) ↦ₘ? 32 ∗ True)%I)
  with "[H12 H13 Hv Hr0 Hr1 Hr2 Hr3 Hs0 Hs1 Hs2 Hs3 Hscratch]"
  as "(Hpair & Hwords & Hlower & Hupper & _)".
 { unfold transactionSourceSignatureWords. zesu_run. }
 iEval (unfold transactionSourceSignatureLoan) in "Hloan".
 iPoseProof ("Hloan" with "Hpair Hwords Hlower") as "Hframe".
 unfold transactionSourceAuthorizationExit.
 iEval (unfold transactionSourceSignatureCommonFrame) in "Hcommon".
 iDestruct "Hcommon" as "(H18 & H144 & H152 & H160 & _)".
 iFrame "Hsys Hsp H18 Hupper Hmmio Htrace H144 H152 H160 Hframe".
 rewrite !reg_col_cons reg_col_nil. zesu_run.
Qed.
Print Assumptions transactions_source_signature_exit.
