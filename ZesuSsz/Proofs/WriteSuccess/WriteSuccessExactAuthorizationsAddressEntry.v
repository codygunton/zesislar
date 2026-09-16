Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratch.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactAuthorizationsOutputWhole
  WriteSuccessExactEncoderU256Spec WriteSuccessObservation WriteSuccessOutputSemantic
  WriteSuccessExactTransactionsGasLoads.

Definition authorizationAddressCallerFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationAddressCallerFrame) := I.

Lemma authorization_u256_to_address `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  authorizationU256Post sp bytes 0 (BV 64 0x155bc)
    (writeOutputEvents (sp + BV 64 1856)%bv (BV 64 20) (take 20 (drop 112 bytes)) tail)
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I -∗
  authorizationWholeOutputEntry sp (BV 64 0x155bc) (BV 64 (mapIoContextAddress defaultMap))
    (sp - BV 64 48)%bv (BV 64 32) bytes tail (authorizationAddressCallerFrame sp P).
Proof.
  iIntros "Hpost". iDestruct "Hpost" as
    "(Hsys & H1 & Hsp & H5 & H10 & H11 & H12 & H13 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hbytes & %Hlen & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H8 & HP & _)".
  have HpayloadLen : length (writeSuccessU256WordsPayload
      (transactionRowWord bytes 0 0) (transactionRowWord bytes 0 8)
      (transactionRowWord bytes 0 16) (transactionRowWord bytes 0 24)) = 32%nat.
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
  have Hsource : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z by bv_solve.
  iEval (rewrite -Hsource) in "Hbytes".
  unfold authorizationWholeOutputEntry. iFrame "Hsys Hsp H8 H1 H5 H10 H11 Hbytes Hmmio Htrace".
  iSplit; first done. iSplit; first (iPureIntro; lia). iSplit; first done.
  iSplit; last done. unfold authorizationAddressCallerFrame. iFrame.
  repeat iSplit; done.
Qed.
Print Assumptions authorization_u256_to_address.
