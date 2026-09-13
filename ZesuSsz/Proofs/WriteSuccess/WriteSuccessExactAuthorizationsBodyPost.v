Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratch.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactEncoderU256Spec
  WriteSuccessExactTransactionsGasLoads WriteSuccessObservation WriteSuccessOutputSemantic.

Definition authorizationBodyPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15614) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗
   authorizationU256Frame sp bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationBodyPost) := I.

Lemma authorization_u256_to_body_post `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  authorizationU256Post sp bytes 64 (BV 64 0x15614) tail
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I -∗
  authorizationBodyPost sp bytes tail P.
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hbytes & %Hlen & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H8 & HP & _)".
  have HpayloadLen : length (writeSuccessU256WordsPayload
      (transactionRowWord bytes 64 0) (transactionRowWord bytes 64 8)
      (transactionRowWord bytes 64 16) (transactionRowWord bytes 64 24)) = 32%nat.
  { unfold writeSuccessU256WordsPayload, writeSuccessPrivateBytes.
    rewrite map_length !app_length.
    cbn [writeSuccessEncodeU64 writeSuccessEncodeLe length]. reflexivity. }
  iPoseProof (call_scratch_reuse sp _ _ HpayloadLen Hlow
    with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  iAssert (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])
    with "[H12 H13]" as "Hpair".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H12".
    - iExists _. iFrame. done.
    - iSplitL "H13"; last done. iExists _. iFrame. done. }
  unfold authorizationBodyPost, authorizationU256Frame. iFrame. repeat iSplit; done.
Qed.
Print Assumptions authorization_u256_to_body_post.
