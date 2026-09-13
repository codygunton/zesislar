Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

Definition encoderU256SimplePost `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   "x12" ↦ᵣ RVal_Bits w2 ∗ "x13" ↦ᵣ RVal_Bits w3 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@encoderU256SimplePost) := I.

Lemma encoder_u256_simple_post `{!islaG Sigma} `{!threadG}
    w0 w1 w2 w3 sp ret tail (P : iProp Sigma) :
  (0x20000000 <= bv_unsigned sp - 48)%Z ->
  encoderU256ExactPost w0 w1 w2 w3 sp ret tail P -∗
  encoderU256SimplePost w0 w1 w2 w3 sp ret tail P.
Proof.
  intros Hlow. iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & HP & _)".
  have Hlen : length (writeSuccessU256WordsPayload w0 w1 w2 w3) = 32%nat.
  { unfold writeSuccessU256WordsPayload, writeSuccessPrivateBytes.
    rewrite map_length !app_length.
    cbn [writeSuccessEncodeU64 writeSuccessEncodeLe length]. reflexivity. }
  iDestruct (byte_array_forget with "Hpayload") as "Hpayload".
  have Haddress : bv_unsigned (sp - BV 64 48)%bv = (bv_unsigned sp - 48)%Z by bv_solve.
  iEval (rewrite Hlen Haddress /=) in "Hpayload".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hret") as "Hret".
  iEval (cbn) in "Hret".
  iEval (replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp - 16 + 8)%Z by lia) in "Hret".
  iPoseProof (mem_mapsto_uninit_combine 8 (bv_unsigned sp - 16) (DfracOwn 1) 16
    with "Hgap Hret") as "Hrest"; first lia.
  iEval (replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp - 48 + 32)%Z by lia) in "Hrest".
  iPoseProof (mem_mapsto_uninit_combine 32 (bv_unsigned sp - 48) (DfracOwn 1) 48
    with "Hpayload Hrest") as "Hscratch"; first lia.
  unfold encoderU256SimplePost. iFrame.
Qed.
Print Assumptions encoder_u256_simple_post.
