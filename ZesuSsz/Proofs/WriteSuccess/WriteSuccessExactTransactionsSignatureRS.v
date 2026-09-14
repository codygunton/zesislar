Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureRCall WriteSuccessExactTransactionsSignatureSCall
  WriteSuccessExactTransactionsSignatureRToS WriteSuccessExactEncoderU256Spec.

Definition transactionSignatureRSEntry `{!islaG Sigma} `{!threadG}
    (sp r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 : bv 64) tail
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
     (writeSuccessU256WordsPayload r0 r1 r2 r3)
     (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
       (writeSuccessU256WordsPayload s0 s1 s2 s3) tail)) ∗
   transactionSignatureRFrame sp r0 r1 r2 r3
     (transactionSignatureSFrame sp s0 s1 s2 s3 P) ∗
   instr_pre 0x1565c (transactionSignatureSPost sp s0 s1 s2 s3 tail
     (transactionSignatureRFrame sp r0 r1 r2 r3 P)) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureRSEntry) := I.

Lemma transactions_signature_rs_correct `{!islaG Sigma} `{!threadG}
    sp r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_84.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_85.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1562c
    (transactionSignatureRSEntry sp r0 r1 r2 r3 s0 s1 s2 s3 oldra old5 tail P).
Proof.
  iStartProof. iIntros "#Hr #Hs #Hencoder #Houtput".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iDestruct "Hentry" as "(Hsys & Hsp & H1 & H5 & Hregs & Hscratch & Hmmio & Htrace & Hframe & Hfinal & _)".
  iPoseProof (transactions_signature_s_call_correct sp s0 s1 s2 s3
    (BV 64 0x15644) (BV 64 (mapIoContextAddress defaultMap)) tail
    (transactionSignatureRFrame sp r0 r1 r2 r3 P)
    with "Hs Hencoder Houtput") as "Hscall".
  iAssert (instr_pre 0x15644 (transactionSignatureRPost sp r0 r1 r2 r3
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload s0 s1 s2 s3) tail)
    (transactionSignatureSFrame sp s0 s1 s2 s3 P))) with "[Hfinal]" as "Hnext".
  { iApply (instr_pre_wand 0x15644 0x15644 false true with "Hscall"); [done | done |].
    iIntros "Hpost". iApply (transactions_signature_r_to_s with "Hpost Hfinal"). }
  iPoseProof (transactions_signature_r_call_correct sp r0 r1 r2 r3 oldra old5
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload s0 s1 s2 s3) tail)
    (transactionSignatureSFrame sp s0 s1 s2 s3 P)
    with "Hr Hencoder Houtput") as "Hrcall".
  iEval (rewrite instr_pre'_eq) in "Hrcall". iApply "Hrcall".
  unfold transactionSignatureREntry. iFrame "Hsys Hsp H1 H5 Hregs Hscratch Hmmio Htrace Hframe Hnext".
Qed.
Print Assumptions transactions_signature_rs_correct.
