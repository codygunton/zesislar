Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesAuthorizationEntry
  WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactTransactionsSourceBlobFeeFrame.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceSignatureLoanSpec.

Lemma transactions_source_signature_factor `{!islaG Sigma} `{!threadG}
    sp base bytes processed index dataBytes accessBytes chainBytes entries blobBytes (Q : iProp Sigma) :
  transactionSourceBlobFeeRetained sp base bytes processed index dataBytes accessBytes
    chainBytes entries blobBytes Q ⊣⊢
  (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   transactionSourceSignatureWords sp bytes index ∗
   (bv_unsigned sp - 48) ↦ₘ? 16 ∗
   transactionSourceSignatureRemainder sp base bytes processed index dataBytes accessBytes
     chainBytes entries blobBytes Q)%I.
Proof.
  iSplit.
  - iIntros "Hframe". iEval (unfold transactionSourceBlobFeeRetained) in "Hframe".
    iDestruct "Hframe" as (pointer storedIndex)
      "(H19 & H22 & Hregs & Hblob & Hcount & Haccess & Hown & HaccessBase & HaccessCount &
        HaccessIndex & Hcopy & Hkeys & Hlower & Hrec0 & Hrec1 & Hrec2 & Htag & Hvalue &
        Hdata & Hchain & Hmemory & _)".
    iEval (unfold transactionFieldSourceFeeRest) in "Hmemory".
    iDestruct "Hmemory" as
      "(Hbytes & Hbase & Hindex & Hauthp & H176 & H184 & H192 & H200 & H208 & H216 &
        H224 & H232 & H240 & Hfour & H32 & H112 & %HdataBounds & %HaccessBounds & HQ & _)".
    iEval (rewrite transactions_source_signature_register_factor) in "Hregs".
    iDestruct "Hregs" as "[Hpair Hregs]".
    iSplitL "Hpair"; first iExact "Hpair".
    iSplitL "H176 H184 H192 H200 H208 H216 H224 H232 H240".
    { unfold transactionSourceSignatureWords. iFrame. }
    iSplitL "Hlower"; first iExact "Hlower".
    unfold transactionSourceSignatureRemainder. iExists pointer, storedIndex.
    iFrame. repeat iSplit; done.
  - iIntros "(Hpair & Hwords & Hlower & Hremaining)".
    iEval (unfold transactionSourceSignatureWords) in "Hwords".
    iDestruct "Hwords" as "(H176 & H184 & H192 & H200 & H208 & H216 & H224 & H232 & H240 & _)".
    iEval (unfold transactionSourceSignatureRemainder) in "Hremaining".
    iDestruct "Hremaining" as (pointer storedIndex)
      "(H19 & H22 & Hregs & Hblob & Hcount & Haccess & Hown & HaccessBase & HaccessCount &
        HaccessIndex & Hcopy & Hkeys & Hrec0 & Hrec1 & Hrec2 & Htag & Hvalue &
        Hdata & Hchain & Hbytes & Hbase & Hindex & Hauthp & Hfour & H32 & H112 &
        %HdataBounds & %HaccessBounds & HQ & _)".
    iAssert (reg_col blobAuthorizationRemainingShapes) with "[Hpair Hregs]" as "HfullRegs".
    { iEval (rewrite transactions_source_signature_register_factor). iFrame. }
    unfold transactionSourceBlobFeeRetained, transactionFieldSourceFeeRest.
    iExists pointer, storedIndex. iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_source_signature_factor.
