Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratch.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactEncoderU256Scratch
  WriteSuccessExactEncoderU256Spec WriteSuccessExactTransactionsGasLoads
  WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma authorization_u256_to_next_u256 `{!islaG Sigma} `{!threadG}
    sp bytes offset ret nextOffset nextRet tail (P : iProp Sigma) :
  authorizationU256Post sp bytes offset ret
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload (transactionRowWord bytes nextOffset 0)
        (transactionRowWord bytes nextOffset 8) (transactionRowWord bytes nextOffset 16)
        (transactionRowWord bytes nextOffset 24)) tail) P -∗
  instr_pre (bv_unsigned nextRet) (authorizationU256Post sp bytes nextOffset nextRet tail P) -∗
  authorizationU256Entry sp ret (BV 64 0x2401a0b8) bytes nextOffset nextRet tail P.
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as
    "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hbytes & %Hlen & %Halign & %Hlow & %Hhigh & HP & _)".
  have HpayloadLen : length (writeSuccessU256WordsPayload
      (transactionRowWord bytes offset 0) (transactionRowWord bytes offset 8)
      (transactionRowWord bytes offset 16) (transactionRowWord bytes offset 24)) = 32%nat.
  { unfold writeSuccessU256WordsPayload, writeSuccessPrivateBytes.
    rewrite map_length !app_length.
    cbn [writeSuccessEncodeU64 writeSuccessEncodeLe length]. reflexivity. }
  iPoseProof (call_scratch_reuse sp ret _ HpayloadLen Hlow
    with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])
    with "[H10 H11 H12 H13]" as "Hwords".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H10".
    - iExists _. iFrame. done.
    - iSplitL "H11".
      + iExists _. iFrame. done.
      + iSplitL "H12".
        * iExists _. iFrame. done.
        * iSplit; last done. iExists _. iFrame. done. }
  unfold authorizationU256Entry. iFrame. repeat iSplit; done.
Qed.
Print Assumptions authorization_u256_to_next_u256.
