Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureVCall WriteSuccessExactTransactionsSignatureRCall
  WriteSuccessExactTransactionsSignatureSCall WriteSuccessExactTransactionsSignatureRS
  WriteSuccessExactTransactionsSignatureVToR WriteSuccessExactEncoderU256Spec
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionSignatureVRSEntry `{!islaG Sigma} `{!threadG}
    (sp value r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 old11 : bv 64) tail
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ reg_col [(KindReg "x10", BitsShape 64)] ∗
   (bv_unsigned sp + 176) ↦ₘ value ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value)))
     (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
       (writeSuccessU256WordsPayload r0 r1 r2 r3)
       (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
         (writeSuccessU256WordsPayload s0 s1 s2 s3) tail))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 184 < 0x40000000⌝ ∗
   transactionSignatureVCaller sp r0 r1 r2 r3 (transactionSignatureSFrame sp s0 s1 s2 s3 P) ∗
   instr_pre 0x1565c (transactionSignatureSPost sp s0 s1 s2 s3 tail
     (transactionSignatureRFrame sp r0 r1 r2 r3 (transactionSignatureVFrame sp value P))) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureVRSEntry) := I.

Lemma transactions_signature_v_to_rs `{!islaG Sigma} `{!threadG}
    (sp value r0 r1 r2 r3 s0 s1 s2 s3 : bv 64) tail (P : iProp Sigma) :
  transactionSignatureVPost sp value
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload r0 r1 r2 r3)
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeSuccessU256WordsPayload s0 s1 s2 s3) tail))
    (transactionSignatureVCaller sp r0 r1 r2 r3 (transactionSignatureSFrame sp s0 s1 s2 s3 P)) -∗
  instr_pre 0x1565c (transactionSignatureSPost sp s0 s1 s2 s3 tail
    (transactionSignatureRFrame sp r0 r1 r2 r3 (transactionSignatureVFrame sp value P))) -∗
  transactionSignatureRSEntry sp r0 r1 r2 r3 s0 s1 s2 s3
    (BV 64 0x1562c) (BV 64 0x2401a0b8) tail (transactionSignatureVFrame sp value P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hvalue & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Hpair & Hlower & Hrframe & _)".
  iDestruct "Hrframe" as "(Hr0 & Hr1 & Hr2 & Hr3 & _ & %Hrlow & %Hrhigh & Hsframe & _)".
  iDestruct "Hsframe" as "(Hs0 & Hs1 & Hs2 & Hs3 & _ & _ & %Hshigh & HP & _)".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I with "[Hlower Hupper]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
    replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia.
    iExact "Hupper". }
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])
    with "[H10 H11 Hpair]" as "Hregs".
  { rewrite !reg_col_cons. iSplitL "H10"; first (iExists _; iFrame; done).
    iSplitL "H11"; last iExact "Hpair". iExists _; iFrame; done. }
  unfold transactionSignatureRSEntry, transactionSignatureRFrame,
    transactionSignatureSFrame, transactionSignatureVFrame.
  iFrame. repeat iSplit; done.
Qed.

Lemma transactions_signature_vrs_correct `{!islaG Sigma} `{!threadG}
    sp value r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 old11 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_83.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_84.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_85.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15620
    (transactionSignatureVRSEntry sp value r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 old11 tail P).
Proof.
  iStartProof. iIntros "#Hv #Hr #Hs #Hint #Hu256 #Houtput".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iDestruct "Hentry" as "(Hsys & Hsp & H1 & H5 & H11 & H10 & Hvalue & Hscratch & Hmmio & Htrace & %Halign & %Hlow & %Hhigh & Hcaller & Hfinal & _)".
  iPoseProof (transactions_signature_rs_correct sp r0 r1 r2 r3 s0 s1 s2 s3
    (BV 64 0x1562c) (BV 64 0x2401a0b8) tail (transactionSignatureVFrame sp value P)
    with "Hr Hs Hu256 Houtput") as "Hrscall".
  iAssert (instr_pre 0x1562c (transactionSignatureVPost sp value
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload r0 r1 r2 r3)
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeSuccessU256WordsPayload s0 s1 s2 s3) tail))
    (transactionSignatureVCaller sp r0 r1 r2 r3 (transactionSignatureSFrame sp s0 s1 s2 s3 P))))
    with "[Hfinal]" as "Hnext".
  { iApply (instr_pre_wand 0x1562c 0x1562c false true with "Hrscall"); [done | done |].
    iIntros "Hpost". iApply (transactions_signature_v_to_rs with "Hpost Hfinal"). }
  iPoseProof (transactions_signature_v_call_correct sp value oldra old5 old11
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload r0 r1 r2 r3)
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeSuccessU256WordsPayload s0 s1 s2 s3) tail))
    (transactionSignatureVCaller sp r0 r1 r2 r3 (transactionSignatureSFrame sp s0 s1 s2 s3 P))
    with "Hv Hint Houtput") as "Hvcall".
  iEval (rewrite instr_pre'_eq) in "Hvcall". iApply "Hvcall".
  unfold transactionSignatureVEntry. iFrame "Hsys Hsp H1 H5 H11 H10 Hvalue Hscratch Hmmio Htrace Hcaller Hnext".
  repeat iSplit; done.
Qed.
Print Assumptions transactions_signature_vrs_correct.
