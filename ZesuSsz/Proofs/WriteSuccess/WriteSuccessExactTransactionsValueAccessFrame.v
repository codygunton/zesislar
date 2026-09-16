Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsValueToData WriteSuccessExactTransactionsValueCall
  WriteSuccessExactTransactionsDataToAccessCount WriteSuccessExactEncoderBytes.

Lemma transactions_bytes_value_access_frame_pack `{!islaG Sigma} `{!threadG}
    (data size sp w0 w1 w2 w3 old6 old9 stack2 count : bv 64)
    bytes tail (P : iProp Sigma) :
  encoderBytesExactPost data size sp (BV 64 0x151c4) bytes old6 data old9 stack2 tail
    ("x22" ↦ᵣ RVal_Bits size ∗
     transactionValueDataSourceFrame sp w0 w1 w2 w3
       (transactionDataAccessCaller sp count P) ∗ True) -∗
  encoderBytesExactPost data size sp (BV 64 0x151c4) bytes old6 data old9 stack2 tail
    ("x22" ↦ᵣ RVal_Bits size ∗
     transactionDataAccessCaller sp count
       (transactionValueDataSourceFrame sp w0 w1 w2 w3 P) ∗ True).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace & Houtput & _)".
  iDestruct "Houtput" as "(H6 & Hsp & H8 & H9 & HcountBytes & Hcountret & Hstack2 & Hsaved9 & Hsaved8 & Hret & Hcaller)".
  iDestruct "Hcaller" as "(H22 & Hsource & _)".
  iDestruct "Hsource" as "(H12 & H13 & Hvalue & _)".
  iDestruct "Hvalue" as "(H18 & H20 & Hword2 & H21 & %Halign & %Hlow & %Hhigh & Haccess & _)".
  iDestruct "Haccess" as "(Hcount & %HaccessAlign & %HaccessLow & %HaccessHigh & HP & _)".
  unfold encoderBytesExactPost, encoderBytesExactOutputResources,
    transactionValueDataSourceFrame, transactionValueFrame, transactionDataAccessCaller.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_bytes_value_access_frame_pack.
