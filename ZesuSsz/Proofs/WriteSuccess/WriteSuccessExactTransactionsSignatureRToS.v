Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratch.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureRCall WriteSuccessExactTransactionsSignatureSCall
  WriteSuccessExactEncoderU256Spec.

Lemma transactions_signature_r_to_s `{!islaG Sigma} `{!threadG}
    (sp r0 r1 r2 r3 s0 s1 s2 s3 : bv 64) tail (P : iProp Sigma) :
  transactionSignatureRPost sp r0 r1 r2 r3
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload s0 s1 s2 s3) tail)
    (transactionSignatureSFrame sp s0 s1 s2 s3 P) -∗
  instr_pre 0x1565c (transactionSignatureSPost sp s0 s1 s2 s3 tail
    (transactionSignatureRFrame sp r0 r1 r2 r3 P)) -∗
  transactionSignatureSEntry sp s0 s1 s2 s3 (BV 64 0x15644) (BV 64 (mapIoContextAddress defaultMap)) tail
    (transactionSignatureRFrame sp r0 r1 r2 r3 P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hr0 & Hr1 & Hr2 & Hr3 & %Halign & %Hlow & %Hhigh & Hsframe & _)".
  iDestruct "Hsframe" as "(Hs0 & Hs1 & Hs2 & Hs3 & _ & _ & %Hshigh & HP & _)".
  have Hlen : length (writeSuccessU256WordsPayload r0 r1 r2 r3) = 32%nat by reflexivity.
  iPoseProof (call_scratch_reuse sp (BV 64 0x15644) _ Hlen Hlow
    with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])
    with "[H10 H11 H12 H13]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil.
    iSplitL "H10"; first (iExists _; iFrame; done).
    iSplitL "H11"; first (iExists _; iFrame; done).
    iSplitL "H12"; first (iExists _; iFrame; done).
    iSplitL "H13"; last done. iExists _; iFrame; done. }
  unfold transactionSignatureSEntry, transactionSignatureSFrame, transactionSignatureRFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_signature_r_to_s.
