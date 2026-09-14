Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureVCall WriteSuccessExactTransactionsSignatureRCall
  WriteSuccessExactEncoderU256Spec.

Definition transactionSignatureVCaller `{!islaG Sigma} `{!threadG}
    (sp r0 r1 r2 r3 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗ transactionSignatureRFrame sp r0 r1 r2 r3 P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureVCaller) := I.

Lemma transactions_signature_v_to_r `{!islaG Sigma} `{!threadG}
    (sp value r0 r1 r2 r3 : bv 64) tail (P : iProp Sigma) :
  transactionSignatureVPost sp value
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload r0 r1 r2 r3) tail)
    (transactionSignatureVCaller sp r0 r1 r2 r3 P) -∗
  instr_pre 0x15644 (transactionSignatureRPost sp r0 r1 r2 r3 tail
    (transactionSignatureVFrame sp value P)) -∗
  transactionSignatureREntry sp r0 r1 r2 r3 (BV 64 0x1562c) (BV 64 (mapIoContextAddress defaultMap)) tail
    (transactionSignatureVFrame sp value P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hvalue & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Hpair & Hlower & Hrframe & _)".
  iDestruct "Hrframe" as "(Hr0 & Hr1 & Hr2 & Hr3 & _ & %Hrlow & %Hrhigh & HP & _)".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I with "[Hlower Hupper]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
    replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia.
    iExact "Hupper". }
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])
    with "[H10 H11 Hpair]" as "Hregs".
  { rewrite !reg_col_cons. iSplitL "H10"; first (iExists _; iFrame; done).
    iSplitL "H11"; last iExact "Hpair". iExists _; iFrame; done. }
  unfold transactionSignatureREntry, transactionSignatureRFrame, transactionSignatureVFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_signature_v_to_r.
