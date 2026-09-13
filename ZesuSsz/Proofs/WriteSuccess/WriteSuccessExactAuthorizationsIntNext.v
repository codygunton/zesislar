Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsInt WriteSuccessExactAuthorizationsU256
  WriteSuccessExactEncoderIntFramedCall WriteSuccessExactTransactionsGasLoads
  WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma authorization_int_to_second_int `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  authorizationIntPost sp bytes (BV 64 0x155d8)
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (bv_unsigned (transactionRowWord bytes 0 104)))) tail) P -∗
  instr_pre 0x155e4 (authorizationIntPost sp bytes (BV 64 0x155e4) tail P) -∗
  authorizationIntEntry sp (BV 64 0x155d8) (BV 64 0x2401a0b8)
    (BV 64 8) bytes 104 (BV 64 0x155e4) tail P.
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hbytes & %Hlen & %Halign & %Hlow & %Hhigh & HP & _)".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)]) with "[H10]" as "H10col".
  { rewrite reg_col_cons reg_col_nil. iSplit; last done. iExists _. iFrame. done. }
  unfold authorizationIntEntry. iFrame. repeat iSplit; done.
Qed.
Print Assumptions authorization_int_to_second_int.
