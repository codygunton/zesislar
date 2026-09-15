Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessExactTransactionsSourceFieldEvents
 WriteSuccessExactAccessListsReturnCount
 WriteSuccessExactAccessListsReturnLoopEntry
 WriteSuccessExactTransactionsDataAccessEntry
 WriteSuccessExactTransactionsSourceFieldLayout
 WriteSuccessExactEncoderIntFramedCall.

Lemma transaction_source_field_post_mono `{!islaG Sigma} `{!threadG}
 sp base bytes processed index dataBytes accessBytes chainBytes entries tail
 (Q R : iProp Sigma) :
 (Q -∗ R) -∗
 transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes
   chainBytes entries tail Q -∗
 transactionSourceFieldPost sp base bytes processed index dataBytes accessBytes
   chainBytes entries tail R.
Proof.
 iIntros "HQR Hpost".
 unfold transactionSourceFieldPost, accessReturnCountPost, encoderIntExactFramedPost.
 iDestruct "Hpost" as
   "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & Hcount & _)".
 iEval (unfold accessReturnCountFrame) in "Hcount".
 iDestruct "Hcount" as "(H22 & H136 & Hloop & _)".
 iEval (unfold accessReturnLoopFrame) in "Hloop".
 iDestruct "Hloop" as (storedIndex old27)
   "(Hgroup & Hunchanged & H19 & H27 & Haccess & Hentries & H256 & H264 &
     H272 & H1744 & Hkeys & Hbounds & _)".
 iEval (unfold accessReturnRuntimeBounds) in "Hbounds".
 iDestruct "Hbounds" as "(%Halign & %Hlow & %Hhigh & Hretained & _)".
 iEval (unfold transactionAccessRetainedMemory) in "Hretained".
 iDestruct "Hretained" as
   "(H1640 & H1648 & H1656 & H120 & H128 & Hdata & Hlower & Hinner & _)".
 iDestruct "Hinner" as "(Hchain & Hsource & _)".
 iEval (unfold transactionFieldSourceRetained) in "Hsource".
 iDestruct "Hsource" as
   "(Hbase & H104 & H248 & H144 & H152 & H160 & H168 & H176 & H184 &
     H192 & H200 & H208 & H216 & H224 & H232 & H240 & H1660 & H1680 &
     H1784 & %HdataBounds & %HaccessBounds & HQ & _)".
 iPoseProof ("HQR" with "HQ") as "HR".
 unfold accessReturnCountFrame, accessReturnLoopFrame, accessReturnRuntimeBounds,
   transactionAccessRetainedMemory, transactionFieldSourceRetained.
 iFrame. repeat iSplit; done.
Qed.
Print Assumptions transaction_source_field_post_mono.
