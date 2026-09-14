Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsInt WriteSuccessExactWithdrawalsOutputWhole
  WriteSuccessExactEncoderIntFramedCall WriteSuccessExactTransactionsGasLoads
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition withdrawalAddressCallerFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalAddressCallerFrame) := I.

Lemma withdrawal_int_to_address_entry `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  withdrawalIntPost sp bytes (BV 64 0x156c0)
    (writeOutputEvents (sp + BV 64 1768)%bv (BV 64 20) (take 20 (drop 24 bytes)) tail)
    ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I -∗
  withdrawalWholeOutputEntry sp (BV 64 0x156c0) (BV 64 0x2401a0b8)
    (sp - BV 64 16)%bv (BV 64 8) bytes tail (withdrawalAddressCallerFrame sp P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hbytes & %Hlen & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H18 & HP & _)".
  have Hsource : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z.
  { clear -Hlow Hhigh. bv_solve. }
  iEval (rewrite -Hsource) in "Hbytes".
  unfold withdrawalWholeOutputEntry, withdrawalAddressCallerFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions withdrawal_int_to_address_entry.
Lemma withdrawal_address_to_int_entry `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 48%nat ->
  withdrawalWholeOutputPost sp bytes
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (bv_unsigned (transactionRowWord bytes 0 16)))) tail)
    (withdrawalAddressCallerFrame sp P) -∗
  instr_pre 0x156dc (withdrawalIntPost sp bytes (BV 64 0x156dc) tail
    ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I) -∗
  withdrawalIntEntry sp (BV 64 0x156d0) (BV 64 0x2401a0b8)
    (BV 64 20) bytes 16 (BV 64 0x156dc) tail
    ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I.
Proof.
  intros Hlen. iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & H18 & Hcaller & _)".
  iDestruct "Hcaller" as "(Hscratch & %Halign & %Hlow & %Hhigh & HP & _)".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)]) with "[H10]" as "H10col".
  { iApply (reg_col_bv_list_shape [("x10", (sp + BV 64 1768)%bv)]). cbn. iFrame. }
  have Hsource : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z.
  { clear -Hlow Hhigh. bv_solve. }
  iEval (rewrite Hsource) in "Hbytes".
  unfold withdrawalIntEntry. iFrame. repeat iSplit; done.
Qed.
Print Assumptions withdrawal_address_to_int_entry.
