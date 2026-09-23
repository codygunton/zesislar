Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratch.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureVCall WriteSuccessExactTransactionsSignatureRCall
  WriteSuccessExactTransactionsSignatureSCall WriteSuccessExactTransactionsBackEdge
  WriteSuccessExactEncoderU256Spec.

Definition transactionSignatureBackEdgeCaller `{!islaG Sigma} `{!threadG}
    (sp index total : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 112) ↦ₘ total ∗ (bv_unsigned sp + 248) ↦ₘ index ∗
   ⌜bv_unsigned sp + 256 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureBackEdgeCaller) := I.

Definition transactionSignatureBackEdgeFrame `{!islaG Sigma} `{!threadG}
    (sp value r0 r1 r2 r3 s0 s1 s2 s3 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits (BV 64 0x1565c) ∗ "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x12" ↦ᵣ RVal_Bits s2 ∗ "x13" ↦ᵣ RVal_Bits s3 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   transactionSignatureSFrame sp s0 s1 s2 s3
     (transactionSignatureRFrame sp r0 r1 r2 r3 (transactionSignatureVFrame sp value P)) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureBackEdgeFrame) := I.

Lemma transactions_signature_to_back_edge `{!islaG Sigma} `{!threadG}
    (sp value r0 r1 r2 r3 s0 s1 s2 s3 index total : bv 64) tail (P : iProp Sigma) :
  transactionSignatureSPost sp s0 s1 s2 s3 tail
    (transactionSignatureRFrame sp r0 r1 r2 r3
      (transactionSignatureVFrame sp value (transactionSignatureBackEdgeCaller sp index total P))) -∗
  instr_pre 0x14f04 (transactionBackEdgePost sp index total
    (transactionSignatureBackEdgeFrame sp value r0 r1 r2 r3 s0 s1 s2 s3 tail P)) -∗
  transactionBackEdgeEntry sp index total
    (transactionSignatureBackEdgeFrame sp value r0 r1 r2 r3 s0 s1 s2 s3 tail P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hsframe & _)".
  iDestruct "Hsframe" as "(Hs0 & Hs1 & Hs2 & Hs3 & %Halign & %Hlow & %Hhigh & Hrframe & _)".
  iDestruct "Hrframe" as "(Hr0 & Hr1 & Hr2 & Hr3 & _ & _ & %Hrhigh & Hvframe & _)".
  iDestruct "Hvframe" as "(Hvalue & _ & %Hvlow & %Hvhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Htotal & Hindex & %Hstackhigh & HP & _)".
  have Hlen : length (writeSuccessU256WordsPayload s0 s1 s2 s3) = 32%nat by reflexivity.
  iPoseProof (call_scratch_reuse sp (BV 64 0x1565c) _ Hlen Hlow
    with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)])
    with "[H10 H11]" as "Hregs".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H10"; first (iExists _; iFrame; done).
    iSplitL "H11"; last done. iExists _; iFrame; done. }
  have Halign8 : bv_unsigned sp `mod` 8 = 0.
  { apply Z.mod_divide; first lia. exists (2 * (bv_unsigned sp / 16)).
    pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)). nia. }
  unfold transactionBackEdgeEntry, transactionSignatureBackEdgeFrame,
    transactionSignatureSFrame, transactionSignatureRFrame, transactionSignatureVFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_signature_to_back_edge.

Lemma transactions_signature_back_edge_continuation `{!islaG Sigma} `{!threadG}
    (sp value r0 r1 r2 r3 s0 s1 s2 s3 index total : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_86.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr 0x14f00 (Some IslaTraces.write_success_28.a14f00.a14f00) -∗
  □ instr_pre 0x14f04 (transactionBackEdgePost sp index total
    (transactionSignatureBackEdgeFrame sp value r0 r1 r2 r3 s0 s1 s2 s3 tail P)) -∗
  □ instr_pre 0x1565c (transactionSignatureSPost sp s0 s1 s2 s3 tail
    (transactionSignatureRFrame sp r0 r1 r2 r3
      (transactionSignatureVFrame sp value (transactionSignatureBackEdgeCaller sp index total P)))).
Proof. move => *. zesu_block. Qed.
Print Assumptions transactions_signature_back_edge_continuation.
