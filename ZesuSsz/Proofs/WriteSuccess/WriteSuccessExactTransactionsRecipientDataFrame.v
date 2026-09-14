Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientValueRegion WriteSuccessExactTransactionsRecipientOutputToValue
  WriteSuccessExactTransactionsRecipientAbsentToValue WriteSuccessExactTransactionsValueDataAccessContinuation
  WriteSuccessExactTransactionsValueCall WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactEncoderU256Spec.

Lemma transactions_value_recipient_data_frame_pack `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 data size count old6 old9 : bv 64)
    (last : bv 32) bytes tail (P : iProp Sigma) :
  transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientValueExitFrame sp tag first second last
      (transactionValueDataAccessCaller data size sp count old6 old9 bytes P)) -∗
  transactionValuePost sp w0 w1 w2 w3 tail
    (transactionValueDataAccessCaller data size sp count old6 old9 bytes
      (transactionRecipientValueExitFrame sp tag first second last P)).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(H18 & H20 & Hword2 & H21 & %Halign & %Hlow & %Hhigh & Hsource & _)".
  destruct (bool_decide (tag = BV 64 0)) eqn:Hcase;
    iEval (rewrite /transactionRecipientValueExitFrame Hcase) in "Hsource";
    iDestruct "Hsource" as "(Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & %HsourceAlign & %HsourceLow & %HsourceHigh & HtagCaller & _)";
    iDestruct "HtagCaller" as "(HtagMemory & HdataCaller & _)";
    iDestruct "HdataCaller" as "(H8 & H22 & H6 & H9 & HdataBytes & %Hlen & Haccess & _)";
    iDestruct "Haccess" as "(Hcount & %HaccessAlign & %HaccessLow & %HaccessHigh & HP & _)";
    unfold transactionValuePost, encoderU256ExactPost, transactionValueFrame,
      transactionValueDataAccessCaller, transactionDataAccessCaller, transactionRecipientValueExitFrame;
    rewrite Hcase;
    unfold transactionRecipientValueSourceFrame, transactionRecipientAbsentValueSourceFrame;
    iFrame; repeat iSplit; done.
Qed.
Print Assumptions transactions_value_recipient_data_frame_pack.
